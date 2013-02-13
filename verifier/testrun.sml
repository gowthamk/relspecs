structure TestRun =
struct	
	(*
	 * structure Control must be seen by this file
	 *)
	open Atoms 
	open CoreML
	open Common 
	datatype testcase =   Int_v of Var.t
						| Bool_v of Var.t
						| Str_v of Var.t
						| Array_v of Var.t 
						| Fun_rv_c of (Var.t * string list * CoreML.Pat.t (* Predicate.t list*))
						| Fun_rv_uc of (Var.t * string list * (Predicate.t list) * Tycon.t)
						
	datatype testcase_value = Int_vl of int
						| Bool_vl of bool
						| Str_vl of string
						| Array_vl of int (* array length *) 

	val dummypat = CoreML.Pat.var (Var.fromString "dummy", Type.var(Tyvar.newNoname {equality = false}))
	
	fun getFunctionBody e = 
			case (Exp.node e) of
				  Exp.Lambda l => 
				  	let val l' = Lambda.dest l
				  	in
				  		getFunctionBody (#body l')
				  	end
				| _ => e
				 
	(*
	 * Collect how called function is called in caller function
	 * @param pat
	 * @param ee is the experssion
	 * @param explist as sideeffects storing all (fun, return site var)s.
	 * @return () but has sideeffects in explist
	 *)
	fun collectFuncalls rpat ee funcalllist = 
 		case (Exp.node ee) of      
		     (Exp.Case {rules, test, ...}) => Vector.foreach (rules, fn {exp, pat, lay} =>
		     	collectFuncalls rpat exp funcalllist
		     )
		   	| (Exp.Let (ds, e)) => 
		   		(Vector.foreach (ds, fn d => collectFuncallsDec d funcalllist);
		   		collectFuncalls rpat e funcalllist)
		   	| (Exp.Seq es) => 
		   		let val es = Vector.toList es
	       			val e' = List.last es
	       			val es' = List.allButLast es
	       			val path = List.foreach (es', fn e'' => collectFuncalls dummypat e'' funcalllist)
	       		in 
	       			collectFuncalls rpat e' funcalllist
	       		end 
		   	| (Exp.App (e1, e2)) => 
		   		let val (_, funpat) = Constraintgen.getFunctioinAppPat ee 
		   		in
		   			HashTable.insert funcalllist (Constraintgen.pat_var funpat, rpat)
		   		end
		   	| e => ()
		
	and collectFuncallsDec d funcalllist =
		case d of
	   		  Dec.Datatype v => ()
	   		| Dec.Exception ca => ()
	   		| Dec.Fun {decs, tyvars, ...} => ()
	   		| Dec.Val {rvbs, tyvars, vbs, ...} => Vector.foreach (vbs, fn ({exp, pat, ...}) => collectFuncalls pat exp funcalllist) 
	
	val hash_fn = HashString.hashString
	
	fun closurevars e fenv funpat = 
		let val boundedvars = HashTable.mkTable (hash_fn o Var.toString, Var.logic_equals) (17, Common.Not_found)
			val freevars = HashTable.mkTable (hash_fn o Var.toString, Var.logic_equals) (17, Common.Not_found)
			val _ = HashTable.insert boundedvars (Constraintgen.pat_var funpat, CoreML.Pat.ty funpat)
			fun lambdaType lambda = 
				let val {argType, body, ...} = CoreML.Lambda.dest lambda
				in
					Type.arrow (argType, CoreML.Exp.ty body)
				end
    		fun loop flag e =
	       		case (Exp.node e) of
	          		  Exp.App (e1, e2) => (loop flag e1; loop flag e2)
	        		| Exp.Case {rules, test, ...} =>
	        			if (Type.isBool (Exp.ty test)) then
	        				(loop flag test;
	        				Vector.foreach (rules, fn rule => loop flag (#exp rule)))
		        		else
		             		(loop true test; 
		             		Vector.foreach (rules, fn pattern => 
		             			CoreML.Pat.foreachVarwithType ((#pat pattern), fn (v, t) => HashTable.insert boundedvars (v, t))
		             		);
		             		Vector.foreach (rules, loop flag o #exp))
			        | Exp.Con _ => ()
			        | Exp.Const _ => ()
			        | Exp.Lambda l => loopLambda flag l
			        | Exp.Let (ds, e) =>
			             (Vector.foreach (ds, loopDec flag)
			              ; loop flag e)
			        | Exp.List es => Vector.foreach (es, loop flag)
			        | Exp.Record r => Record.foreach (r, loop flag)
			        | Exp.Seq es => Vector.foreach (es, loop flag)
			        | Exp.Var (x, _) => if flag then HashTable.insert boundedvars (x (), Exp.ty e) 
			        				else if HashTable.inDomain boundedvars (x ()) then ()
			        				else if (Lightenv.mem (x()) fenv) then ()
				        			else if (String.compare ((Var.toString (x())), "assert") = EQUAL) then ()
			        				else HashTable.insert freevars (x (), Exp.ty e)
			        | _ => (print ("Error: unspported experession " ^ (visitExp e)); assertfalse ())
		    and loopDec flag d =
		       case d of
		          Dec.Datatype _ => ()
		        | Dec.Exception _ => ()
		        | Dec.Fun {decs, ...} => 
		        	(Vector.foreach (decs, fn d => HashTable.insert boundedvars (#var d, lambdaType (#lambda d)));
		        	Vector.foreach (decs, loopLambda flag o #lambda))
		        | Dec.Val {rvbs, vbs, ...} =>
		        	(Vector.foreach (rvbs, fn r => HashTable.insert boundedvars (#var r, lambdaType (#lambda r)));
		        	Vector.foreach (vbs, fn pattern => 
		        		CoreML.Pat.foreachVarwithType ((#pat pattern), fn (v, t) 
		        					=> HashTable.insert boundedvars (v, t))
		        	);
		        	Vector.foreach (rvbs, loopLambda flag o #lambda); 
		        	Vector.foreach (vbs, loop flag o #exp))
		    and loopLambda flag l = 
		    	let val l = Lambda.dest l
		    		val body = #body l
		    	in loop flag body end
		 in
		    (loop false e; (HashTable.listItemsi freevars, HashTable.listItemsi boundedvars)
		    (*List.map (HashTable.listItemsi freevars, (fn (a, b) => a))*)
		    )
		 end
	
	(* Simple wrong implementation; improved later *)
	fun generateFunparamAsserts fr sm = 
		let 
			val assert_list = ref []
			val index = ref 0
			fun generateAsserts' pat f = 
				let val patlist = Frame.bind pat f
				in
					List.foreach (patlist, fn (p, pf) => 
						case pf of 
							  Frame.Fconstr (_, _, (subs, Frame.Qvar (k, _))) => 
							  	let 
							  		(*val k2name = Var.toString k
									val kk = if (String.compare (k2name, "k123") = EQUAL) then (Var.fromString "k117")
											 else k
									*)
							  		val qs = sm k
							  	    val preds = List.map (qs, (Qualifier.apply (Predicate.PVar p)))
							  	in
							  		List.push (assert_list, (List.last preds)) 
							  	end
							| Frame.Fconstr (_, _, (subs, Frame.Qconst qs)) => ()
							| Frame.Fvar (_, (subs, Frame.Qvar (k, _))) =>
								let val qs = sm k
									val preds = List.map (qs, (Qualifier.apply (Predicate.PVar p)))
							  	in
							  		List.push (assert_list, (List.last preds)) 
							  	end
							| _ => ()
					)
				end
			fun generateAsserts fr = (* May wrong implementation here *)(index := 0;
				case fr of 
					Frame.Farrow (SOME pat, f1, f2) => (index := (!index) + 1;
						(generateAsserts' pat f1);
						case f2 of 
							Frame.Farrow _ => generateAsserts f2
							| _ => ()
						)			
					| Frame.Farrow (NONE, f1, f2) => (index := (!index) + 1;
						(generateAsserts' (Pat.var (Var.fromString ("p" ^ (Int.toString (!index))), Type.var(Tyvar.newNoname {equality = false}))) f1);
						case f2 of 
							Frame.Farrow _ => generateAsserts f2
							| _ => ()
						)	
					| _ => (print ("Internal Error when generating function param testcase due to non function frame given"); assertfalse ())
					)
		in
			generateAsserts fr; (!assert_list)
		end
	
	(*
	 * With wrong implementation, the function cannot have record input now.
	 * Generate the test case for a modular function
	 * @param pat(var, ty) the pattern of this function. (var is fun name, ty is the type of the fun)
	 * @param fr is the frame of the function
	 * @param s is the solution map
	 * @return testcase list of (var, exp)
	 *) 
	fun generateTestcase sri pat ee fr pred fenv conditional_fr sm freevars k_fun_pathup_precondition_table =
		let
			val funcalls = HashTable.mkTable (hash_fn o (Var.toString), Var.logic_equals) 
							(7, Not_found)
			val (cvars, bvars) = closurevars ee fenv pat
			val _ = print ("\nAll the free variables in the function " ^ (Var.toString (Constraintgen.pat_var pat)) ^ " is " 
				^ (List.fold (cvars, "", fn ((v, t), str) => (str ^ (Var.toString v) ^ " "))) ^ "\n")
			val ee = getFunctionBody ee
			val _ = collectFuncalls dummypat ee funcalls
			val testcaselist = ref []
			
			val index = ref 0		
			
			fun arrowFrame_params fr = (index := (!index) + 1;
				case fr of 
				(Frame.Farrow (_, f1, f2)) =>
				let 
					val myIndex = (!index)
					val l1 = [] (*(case f1 of
						Frame.Farrow _ => arrowFrame_params f1
						| _ => [])*)
					val l2 = (case f2 of 
						Frame.Farrow _ => arrowFrame_params f2
						| _ => [])
					val recordflag = ref false
					fun genParam f = case f of 
						    Frame.Frecord (fs, _) =>
						    	 let val str = List.fold (fs, "", fn ((ffr, fname), str) => 
						    	 	case (Int.fromString fname) of
						    	 		  SOME iv => (recordflag := false; (str ^ (genParam ffr) ^ ","))
						    	 		| NONE => (recordflag := true; (str ^ fname ^ " = " ^ (genParam ffr) ^ ",")) 
						    	 	)
						    	 	val str_len = String.length str
						    	 	val str = String.substring (str, 0, (str_len-1))
						    	 in 
						    	 	if (!recordflag) then ("{" ^ str ^ "}") (* fake reord *) 
						    	 	else ("(" ^ str ^ ")") (* fake tuple *) 
						    	 end
						  | _ => ("p" ^ (Int.toString (myIndex)))
				in
					(genParam f1) :: (l1 @ l2)
				end  
			| _ => assertfalse ())
			
			fun arrowType_params ty = (index := (!index) + 1;
				case ty of 
				(Type_desc.Tarrow (t1, t2)) =>
				let 
					val myIndex = (!index)
					val l1 = [] (*(case t1 of
						Type_desc.Tarrow _ => arrowType_params t1
						| _ => [])*)
					val l2 = (case t2 of 
						Type_desc.Tarrow _ => arrowType_params t2
						| _ => [])
					val recordflag = ref false
				    fun genParam t = case t of 
						    Type_desc.Ttuple tylist =>
						    	 let val str = List.fold (tylist, "", fn (ty, str) => (case ty of
						    	 	Type_desc.Tfield (name, ty) => ( 
							    	 	case (Int.fromString name) of
							    	 		  SOME iv => (recordflag := false; str ^ (genParam ty) ^ ",")
							    	 		| NONE => (recordflag := true; str ^ name ^ " = " ^ (genParam ty) ^ ",") 
							    	 	)
						    	 	| _ => assertfalse ()
						    	 	))
						    	 	val str_len = String.length str
						    	 	val str = String.substring (str, 0, (str_len-1))
						    	 in 
						    	 	if (!recordflag) then "{" ^ str ^ "}" 
						    	 	else "(" ^ str ^ ")"
						    	 end
						  | _ => ("p" ^ (Int.toString (myIndex)))
				in
					genParam t1 :: (l1 @ l2)
				end  
			| _ => assertfalse ())
			
			(*
			 * Doc: 
			 * 1. How to get vritual funtion parameter constraint?
			 * From the second version of this tool, we will not get function parameter constraint anymore since this procedure
			 * is too too complex.
			 * However, we will directly insert an assertion before the callee function. This assertion is got from the verification
			 * obligation. In a word, the function that would be passed into test unit would not care the constraint of the 
			 * virtual function parameters. 
			 * 2. How to get virtual function return value?
			 * For the virtual function which is called inside the test unit, its return value can be got from the theorem prover.
			 * For the virtual function which is not called inside the test unit, its return value should be got from the 
			 * function parameter chain list. Since our method verify called funtion before callee function, from this chain list,
			 * we know how the return value of the virtual function should be.
			 *)
			fun generateParamTestcase' pat f testcaselist = 
				let 
					val _ = print ("\nworking for  " ^ (Frame.pprint f) ^ "\n")
					val patlist = Frame.bind pat f
				in List.foreach (patlist, fn (p, pf) => 
						(print ("\nTestcase for pat " ^ (Var.toString p) ^ " " ^ (Frame.pprint pf) ^ "\n");
						case pf of 
							Frame.Farrow _ => 
								(print ("\nFarrow testcase for " ^ (Frame.pprint pf) ^ "\n");
								let val iscalled = HashTable.inDomain funcalls p
								in
									if (iscalled) then
										let val rvpat = HashTable.lookup funcalls p
											val params = arrowFrame_params pf
											(*List.map (Frame.arrowframe_pats pf, fn _ => Var.mk_ident "p")*)
											(* val precondition_list = case conditional_fr of 
												  NONE => []
												| SOME (funvar, conditional_fr) =>
													if (Var.logic_equals (funvar, p)) then 
														(* Wrong. Real implementation should consider precondition for function param.
														 * However, it is simple to do that. Just give the actual function to it. 
														 * Our tool could maintain a list of function pass chain list. 
														 * We omit this in current tool. Just consider non-funtional param works for most of the cases.
														 *)
														generateFunparamAsserts conditional_fr sm
													else [] 
											 *)
										in List.push (testcaselist, Fun_rv_c (p, params, rvpat(*, precondition_list*))) end
									else (
										let val params = arrowFrame_params pf
											val rf = Frame.getFrowFr pf
											val ty = case rf of 
												Frame.Fconstr (t, _, _) => t
												| _ => (print "Record type is currently unsupported."; assertfalse ())
											val rvk = Frame.getFrowRefVar pf
											
											val quals = Common.map_partial (fn k => 
															(HashTable.find k_fun_pathup_precondition_table k)
														) rvk
											
											val preds = List.map (quals, fn (_, _, p) => p) 
										in List.push (testcaselist, Fun_rv_uc (p, params, preds, ty)) end 	
									)
								end)
							| Frame.Fconstr (t, _, _) => 
								( 
									if (Tycon.isIntX t) then List.push (testcaselist, Int_v p)
									else if (Tycon.isBool t) then List.push (testcaselist, Bool_v p)
									else if (MLton.equal (t, Tycon.array)) then
										 List.push (testcaselist, Array_v p)
									else (* could be list, vector, or string *)
										(print "Tool will support list, vector, or string in the next version"; assertfalse ())) 
							| Frame.Fvar _ => List.push (testcaselist, Int_v p)
							| _ => (print ("Internal Error when generating param testcase for " ^ (Var.toString p)); assertfalse ())
						)
 					)
 				end
 			
 			
			fun generateClosureTestcase () =
 				List.foreach (cvars, fn (var, ty) => 
 					let val pf = HashTable.lookup freevars var
 					in
 						generateParamTestcase' (Pat.var (var, ty)) pf testcaselist
 					end
 				)
		
			fun generatePropertyClosureTestcase () = 
 				let val predvars = Predicate.vars pred
 					val nonfree_predvars = List.keepAll (predvars, (fn v => not (List.exists (bvars, fn (v', _) => Var.logic_equals (v, v')))))
 				in
 					List.foreach (nonfree_predvars, fn v =>
 						List.push (testcaselist, Int_v v)
 					)
 				end	
		
				
			fun generateParamTestcase fr =
				case fr of 
					Frame.Farrow (SOME pat, f1, f2) => (
						(generateParamTestcase' pat f1 testcaselist);
						case f2 of 
							Frame.Farrow (SOME pat', f1', f2') => pat :: (generateParamTestcase f2)
							| _ => [pat]
						)			
					| Frame.Farrow (NONE, f1, f2) => (print ("Function frame without proper param" ^ (Frame.pprint fr)); assertfalse ())
					| _ => (print ("Internal Error when generating param testcase due to non function frame given"); assertfalse ())
							
			(*fun generateClosureTestcase () =
 				List.foreach (cvars, fn (var, ty) => 
 					let val p = var
 						val mtype = Type.toMyType ty
 					in
	 					case mtype of
	 					Type_desc.Tarrow _ => 
	 						let val _ = print ("function name is " ^ (Var.toString p) ^ "\n")
	 							val _ = List.foreach (HashTable.listItemsi funcalls, fn (f, r) => (print (Var.toString f))) 
	 							val _ = print " printed\n"
	 							val iscalled = HashTable.inDomain funcalls p
	 						in
	 							if (String.compare ((Var.toString p), "loop") = EQUAL) then ()
	 							else if (iscalled) then
	 								let val rvpat = HashTable.lookup funcalls p
	 									val _ = (index := 0)
	 									val params = arrowType_params mtype
	 									(*val precondition_list = case conditional_fr of 
												  NONE => []
												| SOME (funvar, conditional_fr) =>
													if (Var.logic_equals (funvar, p)) then
														generateFunparamAsserts conditional_fr sm
													else [] 
	 									 *)
	 								in List.push (testcaselist, Fun_rv_c (p, params, rvpat(*, precondition_list*))) end
	 							else (print "Wrong. Tool does not support closure function which is not called inside the function"; assertfalse ())
	 						end
	 					| Type_desc.Tconstr (t, _) => 
	 						( 
								if (Tycon.isIntX t) then List.push (testcaselist, Int_v p)
								else if (Tycon.isBool t) then List.push (testcaselist, Bool_v p)
								else if (MLton.equal (t, Tycon.array)) then
									 List.push (testcaselist, Array_v p)
								else (* could be list, vector, or string *)
									(print "Tool will support list, vector, or string in the next version"; assertfalse ())) 
						| Type_desc.Tvar _ => List.push (testcaselist, Int_v p)
						| _ => (print ("Internal Error when generating closure testcase for " ^ (Var.toString var)); assertfalse ())
					end
 				)*)
		in
			let 
				val _ = print ("\nThe fr will be dealt with is " ^ (Frame.pprint fr) ^ "\n")
				val ppats = generateParamTestcase fr 
				val _ = print ("\nFinished.\n")
			in 
				generateClosureTestcase (); generatePropertyClosureTestcase(); (ppats, testcaselist)
			end
		end
		
	fun get_int_value v m = (TheoremProver.get_int_value v m) handle Common.RuntimeError => 0
	fun get_bool_value v m = (TheoremProver.get_bool_value v m) handle Common.RuntimeError => false
	
	fun generateTestcasefile testcaselist model =
		let val outfile = TextIO.openOut ("testcase.sml")
			val _ = TextIO.output (outfile, ("val outfile = TextIO.openOut (\"path\");\n" ^
											 "exception RuntimeError;\n" ^ 
											 "fun assert b = if b then () else (TextIO.output (outfile, \"unsucc\\n\") ; raise RuntimeError)\n")) 
			(*val _ = List.push (testcaselist, (Array_v (Var.fromString "a")))*)
			val tctable = HashTable.mkTable (hash_fn o Var.toString, Var.logic_equals) (17, Common.Not_found)
		    val source = 
		    	(
		    		List.foldr ((!testcaselist), "", fn (tc, str) => 
		    			let val tcp =
		    			case tc of
		    				  Int_v v => (
		    				  	let val value = get_int_value v model
		    				  	in
		    				  	HashTable.insert tctable (v, (Int_vl value)); (* int value *) 
		    				  	"val " ^ (Var.toString v) ^ " = " ^ 
		    					(Int.toString (value)) ^ "\n"
		    				  	end
		    				  ) 
		    				| Bool_v v => ( 
		    					let val value = get_bool_value v model
		    					in
		    					HashTable.insert tctable (v, (Bool_vl value)); (* bool value *)
		    					"val " ^ (Var.toString v) ^ " = "^
		    					(Bool.toString (value)) ^ "\n" 
		    				  	end
		    				  )
		    				| Array_v v => 
		    					let val len = get_int_value (Var.fromString ("Array.length" ^ (Var.toString v) ^ "_")) model
		    						val a = Array.array (len, 0)
		    						val str = "val " ^ (Var.toString v) ^ " = " ^
		    						"Array.fromList" ^ " [" ^ 
		    						(Array.foldr (a, "", fn (i, str) => (Int.toString i) ^ "," ^ str))
		    						val _ = HashTable.insert tctable (v, (Array_vl len)); (* array value *)
		    					in 
		    						if ((Array.length a) > 0) then
		    						(String.substring (str, 0, ((String.size str)-1))) ^
		    						"]" ^ "\n"
		    						else str ^ "]" ^ "\n"
		    					end
					       	| Fun_rv_c (v, params, rvpat(*, precondition_list*)) => (* params could be record but not important *)
					       		"fun " ^ (Var.toString v) ^ " "
					       		^ (List.foldr (params, "", fn (param, str) => ((param) ^ " " ^ str))) ^ "= (\n"
					       		(*^ (if ((List.length precondition_list)=0) then ""
					       		   else List.fold (precondition_list, "", fn (prec, str) => 
					       		   		"assert (" ^ (Predicate.pprint prec) ^ ");\n" ^ str
					       		   )
					       		  )
					       		 *)
					       		^ (let val ty = CoreML.Pat.ty rvpat
					       		  in
					       		  	if (Type.isInt ty) then 
					       		  		let val value = get_int_value (Constraintgen.pat_var rvpat) model
					       		  		in 
					       		  			HashTable.insert tctable (v, (Int_vl value));
					       		  			Int.toString (value) 
					       		  		end
					       		  	else if (Type.isBool ty) then 
					       		  		let val value = get_bool_value (Constraintgen.pat_var rvpat) model
					       		  		in
					       		  			HashTable.insert tctable (v, (Bool_vl value));
					       		  			Bool.toString (value)
					       		  		end
					       		  	else if (Type.isArray ty) then
					       		  		let val len = get_int_value (Var.fromString ("Array.length" ^ (Var.toString (Constraintgen.pat_var rvpat)) ^ "_")) model
				    						val a = Array.array (len, 0)
				    						val str = 
				    						"Array.fromList" ^ " [" ^ 
				    						(Array.foldr (a, "", fn (i, str) => (Int.toString i) ^ "," ^ str))
					       		  		in
					       		  			HashTable.insert tctable (v, (Array_vl len));
				    						if ((Array.length a) > 0) then
				    						(String.substring (str, 0, ((String.size str)-1))) ^
				    						"]" ^ "\n"
				    						else str ^ "]" ^ "\n"
					       		  		end
					       		  	else (print "Error unspported function return type; record is not supported now"; "0"(*assertfalse ()*)) 
					       		  end)
					       		^ ")\n"
					       	| Fun_rv_uc (v, params, preds, t) => (* params could be record but not important *)
					       		"fun " ^ (Var.toString v) ^ " "
					       		^ (List.foldr (params, "", fn (param, str) => ((param) ^ " " ^ str))) ^ "= (\n"
					       		^ (
					       		(* get a reasonable value from theorem prover call *)
				       			if ((List.length preds)=0) then "0" (* any value *)
			       			  	else (
			       			  		TheoremProver.reset();
			       			  		let val predlist = List.fold (HashTable.listItemsi tctable, [], fn ((var, value), predlist) => 
					       				case value of
					       					Int_vl value => ((Predicate.Atom (Predicate.PVar var, Predicate.Eq, Predicate.PInt value)) :: predlist)
					       					| Bool_vl value => 
					       						if value then 
					       							((Predicate.Atom (Predicate.PVar var, Predicate.Eq, Predicate.PInt 1)) :: predlist)
					       						else 
					       							((Predicate.Atom (Predicate.PVar var, Predicate.Eq, Predicate.PInt 0)) :: predlist)
					       					| Array_vl value => 
					       						((Predicate.Atom (Predicate.FunApp ("Array.length", [Predicate.PVar var]), Predicate.Eq, Predicate.PInt value))
					       						:: predlist)
					       					| _ => (print "Imeplemeation incomplete"; assertfalse ())
					       				)
					       				val predlist = List.fold (preds, predlist, fn (pred, predlist) => (pred :: predlist))
					       				val pred = Predicate.big_and predlist
					       				val pred = Predicate.addFunApp pred
					       				val _ = TheoremProver.push pred
					       			in
						       			if (TheoremProver.unsat ()) then (print "System error when generating test case ..."; assertfalse ())
						       			else ( 
						       					if (Tycon.isIntX t) then 
						       						let val value = get_int_value (Constraint.qual_test_var) (TheoremProver.get_model ())
						       						in
					       		  						Int.toString (value) 
						       						end
												else if (Tycon.isBool t) then 
													let val value = get_bool_value (Constraint.qual_test_var) (TheoremProver.get_model ())
													in
														Bool.toString (value)
													end
												else if (MLton.equal (t, Tycon.array)) then				
													let val len = get_int_value (Var.fromString ("Array.length" ^ (Var.toString v) ^ "_")) model
							    						val a = Array.array (len, 0)
							    						val str = 
							    						"Array.fromList" ^ " [" ^ 
							    						(Array.foldr (a, "", fn (i, str) => (Int.toString i) ^ "," ^ str))		    						
							    					in 
							    						if ((Array.length a) > 0) then
							    						(String.substring (str, 0, ((String.size str)-1))) ^
							    						"]" ^ "\n"
							    						else str ^ "]" ^ "\n"
							    					end							
												else (* could be list, vector, or string *)
													(print "Tool will support list, vector, or string in the next version"; assertfalse ())
				       			  		) (* end of second if-else *)
				       			  	end
			       			  	) (* end of first if-else *) 
					       		)
					       		^ ")\n"
					        | _ => (print "Has type not supported by current tool."; assertfalse ())
					    in tcp ^ str end 
		    		)
		    	)
		in
			(TextIO.output (outfile, source)   	
		    ;
		    TextIO.flushOut (outfile))
		end
	
	
	fun extendDecList decs targetFunname recflag = 
		let
			fun loop e =
               let val d = case (Exp.node e) of
                  Exp.App (e1, e2) => 
                  	let val d1 = loop e1
                  	in
                  		case d1 of 
                  			SOME d1 => SOME d1
                  			| NONE => loop e2
                  	end
                | Exp.Case {kind, lay, nest, noMatch, nonexhaustiveExnMatch, nonexhaustiveMatch, redundantMatch,
                		region, rules, test} =>   
                	let val d1 = loop test
                	in
                		case d1 of 
                			SOME d1 => SOME d1
                			| NONE => Vector.fold (rules, NONE, fn ({exp, lay, pat}, d) => 
                				case d of 
                					SOME d => SOME d
                					| NONE => loop exp
                			)
                	end       
                | Exp.Con c => NONE
                | Exp.Const c => NONE
                | Exp.Lambda l => loopLambda l
                | Exp.Let (ds, e) => 
                	let val d1 = Vector.fold (ds, NONE, fn (d, d') => 
                			case d' of 
                				SOME d' => SOME d'
                				| NONE => loopDec d false
                		)
                	in
                		case d1 of 
                			SOME d1 => SOME d1
                			| NONE => loop e
                	end
                | Exp.List es => Vector.fold (es, NONE, fn (e, d) => 
                	case d of 
                		SOME d=> SOME d
                		| NONE => loop e
                ) 
                | Exp.Record r => Vector.fold (Record.toVector r, NONE, fn ((a, b), d) =>
                	case d of 
                		SOME d => SOME d
                		| NONE => loop b
                ) 
                | Exp.Seq es => Vector.fold (es, NONE, fn (e, d) => 
                	case d of 
                		SOME d => SOME d
                		| NONE => loop e
                ) 
                | Exp.Var v => NONE
                | e1 => NONE
               in d end          
            and loopDec d toplevel =
               case d of
                  Dec.Datatype dt => NONE
                | Dec.Exception et => NONE
                | Dec.Fun {decs, tyvars} => 
                	if (Vector.exists (decs, fn dec => 
		                		let val funname = (#var dec)
		                		in
		                			Var.logic_equals (funname, targetFunname)
		                		end
							)) then
						SOME (d, toplevel)
					else Vector.fold (decs, NONE, fn (dec, d) => 
						case d of 
							SOME d => SOME d
							| NONE => 
								let val l = (#lambda dec)
				                	val e = (#body (Lambda.dest l))
				                in loop e end
					)
                | Dec.Val {nonexhaustiveExnMatch, nonexhaustiveMatch, rvbs, tyvars, vbs} =>
                	if (Vector.exists (rvbs, fn rvb =>
								let val funname = (#var rvb)
								in
									Var.logic_equals (funname, targetFunname)
								end
							)) then
						SOME (d, toplevel)
					else 
						let val d = Vector.fold (rvbs, NONE, fn (rvb, d) => 
						case d of 
							SOME d => SOME d
							| NONE => 
								let val l = (#lambda rvb)
									val e = (#body (Lambda.dest l))
								in loop e end
						)
						in
							case d of 
								SOME d => SOME d
								| NONE => 
									Vector.fold (vbs, NONE, fn (vb, d) => 
										case d of 
											SOME d => SOME d
											| NONE => loop (#exp vb)
									)  
						end
 
            and loopLambda l = 
            	let val {arg, argType, body, mayInline} = Lambda.dest l
            	in loop body end
		
			val d = List.fold (decs, NONE, fn (dec, d) =>
				case d of 
					SOME d => SOME d
					| NONE => loopDec dec true
			)
			val (d, toplevel) = case d of 
				SOME (d, toplevel) => (d, toplevel)
				| NONE => (print "unfound tested modular function"; assertfalse ())
				
			
			val d' = if recflag then (
					case d of 
						Dec.Fun {decs, tyvars} =>  
							Dec.Fun {decs=Vector.map (decs, fn dec => 
		            		let val funname = (#var dec)
		            		in
		            			{lambda = (#lambda dec), var = Var.fromString ((Var.toString funname) ^ "_test")}
		            		end 
		            		), tyvars=tyvars}
					| Dec.Val {nonexhaustiveExnMatch, nonexhaustiveMatch, rvbs, tyvars, vbs} =>
						Dec.Val {nonexhaustiveExnMatch=nonexhaustiveExnMatch, 
		            		nonexhaustiveMatch=nonexhaustiveMatch, 
		            		rvbs=Vector.map (rvbs, fn rvb => 
		            			let val funname = #var rvb
		            			in
		            				{lambda = (#lambda rvb),  var= Var.fromString ((Var.toString funname) ^ "_test")}
		            			end 
		            			), 
		            		tyvars=tyvars, 
		            		vbs=vbs}
					| _ => assertfalse ()
					)
				else d
			val newFunname = if recflag then Var.fromString ((Var.toString targetFunname) ^ "_test") else targetFunname 
		in
			if toplevel then 
				if recflag then (newFunname, List.append (decs, [d']))
				else (newFunname, decs)
			else 
				if recflag then (newFunname, List.append (decs, [d, d']))
				else (newFunname, List.append (decs, [d']))		
		end
	
	
	(*
	fun extendDecListForRec decs targetFunname = 
		let 
			val newFunname = Var.fromString ((Var.toString targetFunname) ^ "_test")
			val d = 
				List.peek (decs, fn dec =>
					case dec of 
						  Dec.Fun {decs, tyvars} => 
							Vector.exists (decs, fn dec => 
		                		let val funname = (#var dec)
		                			val l = (#lambda dec)
		                			val e = (#body (Lambda.dest l))
		                		in
		                			Var.logic_equals (funname, targetFunname)
		                		end
							)
						| Dec.Val {nonexhaustiveExnMatch, nonexhaustiveMatch, rvbs, tyvars, vbs} =>
							Vector.exists (rvbs, fn rvb =>
								let val funname = (#var rvb)
								in
									Var.logic_equals (funname, targetFunname)
								end
							)
						| _ => false
				)
			val d = case d of SOME d => d | NONE => assertfalse ()
			val d = 
				case d of 
					Dec.Fun {decs, tyvars} =>  
						Dec.Fun {decs=Vector.map (decs, fn dec => 
	            		let val funname = (#var dec)
	            		in
	            			{lambda = (#lambda dec), var = Var.fromString ((Var.toString funname) ^ "_test")}
	            		end 
	            		), tyvars=tyvars}
				| Dec.Val {nonexhaustiveExnMatch, nonexhaustiveMatch, rvbs, tyvars, vbs} =>
					Dec.Val {nonexhaustiveExnMatch=nonexhaustiveExnMatch, 
	            		nonexhaustiveMatch=nonexhaustiveMatch, 
	            		rvbs=Vector.map (rvbs, fn rvb => 
	            			let val funname = #var rvb
	            			in
	            				{lambda = (#lambda rvb),  var= Var.fromString ((Var.toString funname) ^ "_test")}
	            			end 
	            			), 
	            		tyvars=tyvars, 
	            		vbs=vbs}
				| _ => assertfalse ()	
		in
			(newFunname, List.append (decs, [d]))
		end
	*)
	
	(*
	 * Add print to file statement to each if-then-else statement
	 * @param decs the program
	 * @param pat the pat of the main test target function
	 * @param recflag indicates whether the main target function is recursive or not
	 * @param call_funvar indicate if an assertion should be inserted into the body of the function 
	 *) 
	fun generateSMLfile decs pat recflag call_info = 
		let	
			val targetFunname = case CoreML.Pat.node pat of
				CoreML.Pat.Var var => var
				| _ => assertfalse ()	
			(*val (targetFunname, decs) = if recflag then 
				extendDecListForRec decs targetFunname
			else (targetFunname, decs)*)
			
			val (targetFunname, decs) = extendDecList decs targetFunname recflag
			
			val dummy_ty = Type.var(Tyvar.newNoname {equality = false})
			val outfiletrue = Exp.App (Exp.var ((Var.fromString "TextIO.output"), dummy_ty), Exp.var (Var.fromString "(outfile, \"true\\n\")", dummy_ty)) 
			val outfilefalse = Exp.App (Exp.var ((Var.fromString "TextIO.output"), dummy_ty), Exp.var (Var.fromString "(outfile, \"false\\n\")", dummy_ty)) 
			
		
			val _ = print ("\ncall_info: " ^ (
				case call_info of 
					SOME (call_funvar, pred) => ((Var.toString call_funvar) ^ " and pred: "^ (Predicate.pprint pred)) 
					| NONE => "NONE"
			))
			
			(*val app_pending = HashTable.mkTable (hash_fn o (Var.toString), Var.logic_equals) 
							(7, Not_found)
			*)
			fun loop flag e =
               let val expnode = case (Exp.node e) of
                  Exp.App (e1, e2) => (
                  	let val (funname, funpat) = Constraintgen.getFunctioinAppPat e
                  		val funvar = Constraintgen.pat_var funpat
       
                  		val e' = Exp.App (loop flag e1, loop flag e2)
                  		val ty = Exp.ty e
                  		val ise1Var = case (Exp.node e1) of Exp.Var _ => true | _ => false
                  	in
                  		case call_info of
                  			SOME (call_funvar, pred) =>
                  				if ((*String.equals (funname, "assert") orelse*)
                  					(Var.logic_equals (funvar, call_funvar) andalso ise1Var)) then (
                  					(*HashTable.insert app_pending (funvar, ());*)
                  					if (String.equals (Var.toString funvar, "assert")) then (
                  					Exp.make (Exp.Seq (Vector.new2 
                  						(Exp.make (e', ty), 
                  						 Exp.make (Exp.App (Exp.var (Var.fromString "TextIO.output", dummy_ty), 
                  						 					Exp.var (Var.fromString "(outfile, \"succ\\n\")", dummy_ty)), dummy_ty)
                  						 )), ty)
                  					)	 
                  					else (
                  					Exp.make (Exp.Seq (Vector.new3 
                  						(Exp.make (Exp.App (Exp.var (Var.fromString "assert", dummy_ty), 
                  								   			Exp.var (Var.fromString (Predicate.pprint pred), dummy_ty)),
                  								   dummy_ty), 
                  						 Exp.make (Exp.App (Exp.var (Var.fromString "TextIO.output", dummy_ty), 
                  						 		   			Exp.var (Var.fromString "(outfile, \"succ\\n\")", dummy_ty)),
                  						 		   dummy_ty),
                  						 Exp.make (e', dummy_ty))), ty)
                  					) (* end of last else *)
                  					) (* end of first then *)
                  				else Exp.make (e', ty)
                  			| NONE => Exp.make (e', ty)
                  	end
                  )
                | Exp.Case {kind, lay, nest, noMatch, nonexhaustiveExnMatch, nonexhaustiveMatch, redundantMatch,
                		region, rules, test} =>          
                	if (Type.isBool (Exp.ty test) andalso flag) then
                		let val rules = Vector.map (rules, fn {exp, lay, pat} => 
                			case (CoreML.Pat.node pat) of 
					  			CoreML.Pat.Con {arg=arg',con=con',targs=targs'} => (
					  				let val ty = Exp.ty e
					  				in
					  				(case Con.toString (con') of
						  		  		  "true" => {exp=Exp.make (Exp.Seq (Vector.new2 (Exp.make (outfiletrue, dummy_ty), 
						  		  		  		loop flag exp)), ty), lay=lay, pat=pat}
						  				| "false" => {exp=Exp.make (Exp.Seq (Vector.new2 (Exp.make (outfilefalse, dummy_ty),
						  						loop flag exp)), ty), lay=lay, pat=pat}
						  				| _ => (print "generateSMLfile if-then-else error"; assertfalse ()))
						  			end
						  			)
						  		| _ => (print ("generateSMLfile if-then-else error"); assertfalse ())
                		 )
                		in Exp.make (Exp.Case {kind=kind, lay=lay, nest=nest, noMatch=noMatch, 
                					nonexhaustiveExnMatch=nonexhaustiveExnMatch, 
                					nonexhaustiveMatch=nonexhaustiveMatch,
                					redundantMatch=redundantMatch,
                			  		region=region, rules=rules, test=loop flag test}, Exp.ty e)
                		end
                	else
                		Exp.make (Exp.Case {kind=kind, lay=lay, nest=nest, noMatch=noMatch, 
                					nonexhaustiveExnMatch=nonexhaustiveExnMatch, 
                					nonexhaustiveMatch=nonexhaustiveMatch,
                					redundantMatch=redundantMatch,
                			  		region=region, rules= Vector.map (rules, fn {exp, lay, pat} =>
                			  			{exp=loop flag exp, lay=lay, pat=pat}
                			  		), 
                			  		test=loop flag test}, Exp.ty e)
                | Exp.Con c => Exp.make (Exp.Con c, Exp.ty e)
                | Exp.Const c => Exp.make (Exp.Const c, Exp.ty e)
                | Exp.Lambda l => Exp.make (Exp.Lambda (loopLambda flag l), Exp.ty e)
                | Exp.Let (ds, e) => Exp.make (Exp.Let (Vector.map (ds, loopDec flag), loop flag e), Exp.ty e)
                | Exp.List es => Exp.make (Exp.List (Vector.map (es, loop flag)), Exp.ty e)
                | Exp.Record r => Exp.make (Exp.Record (Record.map (r, loop flag)), Exp.ty e)
                | Exp.Seq es => Exp.make (Exp.Seq (Vector.map (es, loop flag)), Exp.ty e)
                | Exp.Var v => Exp.make (Exp.Var v, Exp.ty e)
                | e1 => Exp.make (e1, Exp.ty e)
               in expnode end          
            and loopDec flag d =
               case d of
                  Dec.Datatype dt => Dec.Datatype dt
                | Dec.Exception et => Dec.Exception et
                | Dec.Fun {decs, tyvars} => 
                	Dec.Fun {decs=Vector.map (decs, fn dec => 
                		let val funname = (#var dec)
                			val b = Var.logic_equals (funname, targetFunname)
                		in
                            print ("\nlooping function " ^ (Var.toString funname) ^ "\n");
                			{lambda = loopLambda b (#lambda dec), var=(#var dec)}
                		end 
                		), tyvars=tyvars}
                | Dec.Val {nonexhaustiveExnMatch, nonexhaustiveMatch, rvbs, tyvars, vbs} =>
                	Dec.Val {nonexhaustiveExnMatch=nonexhaustiveExnMatch, 
                		nonexhaustiveMatch=nonexhaustiveMatch, 
                		rvbs=Vector.map (rvbs, fn rvb => 
                			let val funname = #var rvb
                				val b = Var.logic_equals (funname, targetFunname)
                			in
                				print ("\nlooping function " ^ (Var.toString funname) ^ "\n");
                				{lambda=loopLambda b (#lambda rvb),  var=(#var rvb)}
                			end 
                			), 
                		tyvars=tyvars, 
                		vbs=Vector.map (vbs, fn vb => {exp= loop flag (#exp vb),
                             lay=(#lay vb),
                             nest=(#nest vb),
                             pat=(#pat vb),
                             patRegion=(#patRegion vb)})
                         }
            and loopLambda flag l = 
            	let val {arg, argType, body, mayInline} = Lambda.dest l
            	in 
            	(Lambda.make {arg=arg, argType=argType, body=loop flag body, mayInline=mayInline})
            	end
		
			val decs = List.map (decs, loopDec false)
			val program_text = List.fold (decs, "", fn (dec, str) => (str ^ (CoreML.visitDec dec)))
			val outfile = TextIO.openOut ("program.sml")
		in
			(* print out the sml file *)
			TextIO.output (outfile, program_text);
			TextIO.flushOut (outfile)
			(*(print "save program.sml"; Control.saveToMyFile ("program", {suffix = "sml"}, Control.ML, coreML,
        		Control.Layouts CoreML.Program.layouts))*)
		end
	
	(*
	 * @param pat is the testing function pat
	 * @param ppats is the actuals params to this function
	 * @param flag is the flag saying if it is postcondition check
	 *)
	fun generateCallfile pat ppats post pred recflag = 
		let val outfile = TextIO.openOut ("call.sml") 
			val callfunname = 
				if recflag then
					(Var.toString (Constraintgen.pat_var pat)) ^ "_test"
				else 
					(Var.toString (Constraintgen.pat_var pat))
		    val source = case post of 
		    	  true =>
		    		"let val dummy = " ^ callfunname ^ 
		    		(List.fold (ppats, "", fn (ppat, str) => (str ^ " " ^ (Var.toString (Constraintgen.pat_var ppat))))) (* should support record later *)
		    		^ " in assert (" ^ (Predicate.pprint pred) ^ ") end; TextIO.output (outfile, \"succ\\n\"); \n"
		    	| false => 
		    		callfunname ^ 
		    		(List.fold (ppats, "", fn (ppat, str) => (str ^ " " ^ (Var.toString (Constraintgen.pat_var ppat))))) (* should support record later *)
		    		^ ("; \n")
		    val source = source ^ "TextIO.flushOut (outfile);"
		in
			(TextIO.output (outfile, source);
		    TextIO.flushOut (outfile))
		end
	
	 (*
	  * generate the structure of the sml program that would be tested.
	  * @param decs the original sml program structure
	  * @param testcase the testcase to this program
	  * @param call_info is the function call of inside the test unit that a precondition should be set
	  * @return the modeified Dec.t list that would hardcode the testcase in and print each if-else-then statement and match-case statement into a file
	  *)
	fun generateProgram sri decs pat exp fr post pred recflag fenv model preconditional_fr sm freevars k_fun_pathup_precondition_table =
	 	let val (ppats, testcase) = generateTestcase sri pat exp fr pred fenv preconditional_fr sm freevars k_fun_pathup_precondition_table
	 		val _ = print "\ntestcase generated\n"
	 	in
		 	(generateTestcasefile testcase model;
		 	print "\ntestcase file genearted\n";
		 	generateSMLfile decs pat recflag (case preconditional_fr of SOME (funvar, conditional_fr) => SOME (funvar, pred) | NONE => NONE);
		 	print "\nsml file generated\n";
		 	generateCallfile pat ppats post pred recflag;
		 	print "\ncall file generated\n")  
	 	end
			
	fun readPath () =
		let val infile = TextIO.openIn "path"
			val paths = ref []
			(* The first two line of the file are preserved for system use *)
			(* val _ = TextIO.inputLine infile
			val _ = TextIO.inputLine infile
			val _ = print "First two lines readed.\n" *)
			fun readPath' () = 
				let val line = TextIO.inputLine infile
				in
					case line of 
						  NONE => () 
						| SOME line => (List.push (paths, line); print (line ^ "\n"); readPath' ())
				end
			val _ = readPath' ()
			val _ = print "All readed. \n" 
			val paths = List.rev (!paths)
			val paths_len = List.length paths
			val (paths, r) = List.splitAt (paths, paths_len-1)
		in
			(List.keepAll (paths, fn p => (not (String.hasPrefix (p, {prefix = "succ"}))))) @ r
			(*let 
				val _ = readPath' ()
				val _ = print "All readed.\n"
				val ps = List.rev (!paths)
				val psend = if ((List.length ps)=0) then ""
							else List.last ps
				val _ = print ("psend: " ^ psend ^ (Int.toString (String.length psend)) ^ "\n")
			in
				if (String.compare (psend, "succ") = EQUAL orelse String.compare (psend, "unsucc") = EQUAL) then ps
				else List.append (ps, ["unsucc"])
			end*)
		end
		
	fun compileExecute sri decs pat exp fr post pred recflag fenv model preconditional_fr sm freevars k_fun_pathup_precondition_table = 
		let val _ = generateProgram sri decs pat exp fr post pred recflag fenv model preconditional_fr sm freevars k_fun_pathup_precondition_table
			val hndl = DynLink.dlopen ("./executeSML.dylib", DynLink.RTLD_LAZY)

			val execute = _import * : DynLink.fptr -> string -> unit;
			val make_execute = DynLink.dlsym (hndl, "execute");
			val _ = (execute make_execute) ("compile");
			val _ = DynLink.dlclose hndl
			val _ = print "Testing finished.\n"
   			val path = readPath ()
   			val _ = print "Testing path readed. \n"
			(*val result = List.last path
			val path = List.allButLast path
			val _ = print "Done.\n"
			*)
		in
			List.foreach (path, print); (* ((String.compare (result, "succ") = EQUAL), path) *)
			path
		end
end