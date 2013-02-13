structure VerificationCondition =
	struct
    	
    	(*
		 * Convert a binding_cnst into verfication condition that can be sovled by a theorem prover
		 * @param bcnst it binding_cnst: 
		 *	type binding_cnst = (* each for one binding including top level bindings and all the functions both toplevel or local *)
		 *		{
		 *			bid : binding_id (* binding_id used for the function (binding) worklist *)
		 *			pat : Pat.t (* the name of the binding *)
		 *			exp : Exp.t (* the expression of the binding *)
		 *			sri : ref_index (* the constraints *)
		 *		}
		 *  and type ref_index =  
		 * 		{ 
		 * 			orig: (subref_id, labeled_constraint) hash_table, (* id -> orig *)
		 *   		cnst: (subref_id, refinement_constraint) hash_table,  (* id -> refinement_constraint *) 
		 *   		rank: (subref_id, (int * bool * fc_id)) hash_table,  (* id -> dependency rank *)
		 *   		depm: (subref_id, subref_id list) hash_table,         (* id -> successor ids *)
		 *   		pend: (subref_id, unit) hash_table  (* id -> is in wkl ? *)
		 *   		rhs_km : (Var.t, subref_id list) hash_table
		 * 		}
		 * @param s is a hashtable of solution map which mapping refinements into qualifiers
		 * @return the verfication condition in first order preicatate
		 *)   
       
       
       	open Atoms
       	open CoreML
       	open Common
		structure P = Predicate
		structure Le = Lightenv
		structure B = Builtin 
		structure F = Frame
		structure Ct = Constraint
		structure TP = TheoremProver      
		
		
		val nb_iteration = ref 0
		val t_iteration = ref (Time.zero)
		fun incr_t_iteration t_start = (t_iteration := Time.+(!t_iteration, Time.-(Time.now(), t_start)))
		
		val intermediate_nb_refinement = ref 0;
		val intermediate_max_refinement_len = ref 0;
		
		fun reset () = (
			nb_iteration := 0;
			t_iteration := Time.zero;
			intermediate_nb_refinement := 0;
			intermediate_max_refinement_len := 0
		)
		
		val print_stats = fn () => (
		  print ("Verification stats:" ^ (Int.toString (!nb_iteration)) ^ " iterations, "
		  						^ (LargeReal.toString ((Time.toReal (!t_iteration)))) ^ " cegar time in seconds\n")
		  )
		
		val hash_fn = HashString.hashString
		
        fun implies_tp lhs addingfunapps = 
			let 
				val tpimplies = if ((List.length addingfunapps)=0) then 
					TP.implies (Predicate.addFunApp lhs)
					else TP.implies (Predicate.big_and ((Predicate.addFunApp lhs) :: addingfunapps))
			in
				fn p => ((*print ("p is " ^ (Predicate.pprint p) ^ "\n");*) tpimplies p)
			end
			
		(* recording how a precondition refinement is set for a function *)
       	val k_precondition_table = HashTable.mkTable (hash_fn o (Var.toString), Var.logic_equals) (17, Not_found)
		
		fun ho_args_fromty ty funvar = 
			let fun ho_args_fromty' ty index = 
					case ty of 
				 		  Type_desc.Tarrow (t1, t2) => 
				 			let val l1 = [Predicate.FunApp (("arg" ^ (Int.toString index)), [Predicate.PVar funvar])]
				 				val l2 = case t2 of 
				 					  Type_desc.Tarrow _ => ho_args_fromty' t2 (index+1)
				 					| _ => []
				 			in
				 				l1 @ l2
							end 
						| _ => (print "Not arrow given for a type\n"; assertfalse ())
			in
				ho_args_fromty' ty 0
			end
		
		 
        (*
         * @param sri is indexed constraints (types shown above)
         * @param cnst is the starting constraint from which we build verification condition
         * @param sm is the solution map
         * @return verification condition which is purely first order logic predicate
         * @non_convergence_table  is used to record repeated recursive function precondition check. 
         * Note: If the size of the predicate exceeds the predefined threshold. Size of the predicate is the size of the list of all its And conjuncts.  
         *)
        fun verify (bcnst as {bid, pat, exp, fr, sri, ifb}) s back_s procedureflag bindingframe paths fenv decs freevars totalvars 
        		var_frame frame_vars hov force_convergence_table non_convergence_table polymatching_table parameterIndex_table = 
        	let val built_ins = ["tabulate_0", "array_0", "sub_0", "update_0", "copy_0", "appi_0", "length_0", "foldl_0", "app_0", "size", "sub_1",
        						"array_1", "update_1", "nRows_0", "nCols_0", "sin", "cos", "real", "ignore_0", "make_str"]
        		val sm = (Constraint.solution_map s)
        		val sri = (#sri bcnst)
        		val w = Constraint.make_initial_worklist sri
				
				val pat = #pat bcnst
				val fr = #fr bcnst
				
				val _ = (nb_iteration := (!nb_iteration) + 1)
				
				fun isRecursiveFun bodyExp funvar = 
					let val recflag = ref false
					in
						(Exp.foreachVar (bodyExp, (fn mvar => if Var.logic_equals(mvar, funvar) 
															then recflag := true 
															else ())
						); !recflag)
					end
				val recflag = isRecursiveFun (#exp bcnst) (Constraintgen.pat_var (#pat bcnst)) 	
				
				fun getk2 r2 = 
					case r2 of 
						(_, F.Qvar (k2, _)) => 
							if (HashTable.inDomain polymatching_table k2) then HashTable.lookup polymatching_table k2
							else k2
						| _ => (print "Can't get k refinement var from refinement"; assertfalse())
						
				fun getSub2s r2 = 
					case r2 of 
						(sub2s, F.Qvar (k2, _)) => sub2s
						| _ => (print "Can't get k refinement subs"; assertfalse())
				
				(* This function is discarded
				fun isFunSubtypingCheck sri c = 
					case c of
					(Ct.SubRef (env,g,r1,r2,funflag,recordIndex,con,conrecordIndex,SOME id)) => 
					if funflag then
						let val exp = Constraint.getExp sri c
							fun check varf vart = 
								if (Type.isArrow (vart)) then
									let val var = varf
										val varframe = HashTable.lookup totalvars var
										val k1 = Frame.getFrowRefVar varframe
										val k2 = getk2 r1
									in
										if (Var.logic_equals (k1, k2)) then false
										else true
									end
								else true 
						in
							case (Exp.node exp) of
								Exp.App (e1, e2) => (
									case (Exp.node e2) of 
										Exp.Record r => 
											let val argument = (fn (a, b) => b) (List.nth (Vector.toList (Record.toVector r), recordIndex-1))
											in 
												case (Exp.node argument) of
													Exp.Var (varf, vart) => check (varf ()) (Exp.ty argument)
													| _ => (print ("Unaccepted nested record sytax" ^ (CoreML.visitExp argument)); assertfalse ())
											end
										| Exp.Var (varf, vart)=> (* We need to consider a virtual parameter fun's return val as ordinary parameter *)
											check (varf()) (Exp.ty e2)
										| _ => true (* Should not reach here *)	
								)
								| _ => true
						end
					else false
					| _ => (print ("Internal error of wrong subref constraint"); assertfalse ())
				*)					
						
				
				(* constraint table, so open constraint is folded and will not be verified again
				 * However, closed constraint must be verified separately
				 *)
				val conpending = HashTable.mkTable (hash_fn o (Int.toString), (op=)) (117, Not_found)
        		
        		(* recording functional refinement path up pred *)
        		val k_fun_pathup_precondition_table = HashTable.mkTable (hash_fn o (Var.toString), Var.logic_equals) (17, Not_found)
        		
        		
        		(* printing the counterexample path with variable assignemnt *)
        		fun print_ce cepath model = 
        			let fun print_assignment v ty model =  
        					case (Type.toMyType ty) of 
        						Type_desc.Tarrow _ => ""
        							(*print ("P1" ^ (Var.toString v) ^ " = " ^ (Int.toString (TheoremProver.get_int_value (Var.fromString ) model)) ^ "; ")*)
        						| Type_desc.Tconstr (t, _) => ((
        							if (Tycon.isIntX t) then
        								((Var.toString v) ^ " = " ^ (Int.toString (TheoremProver.get_int_value v model)) ^ "; ")
									else if (Tycon.isBool t) then 
										((Var.toString v) ^ " = " ^ (Bool.toString (TheoremProver.get_bool_value v model)) ^ "; ")
									else if (MLton.equal (t, Tycon.array)) then
									 	("len " ^ (Var.toString v) ^ " = " 
									 		^ (Int.toString (TheoremProver.get_int_value  (Var.fromString ("Array.length" ^ (Var.toString v) ^ "_")) model)) ^ "; ")
									else ((Var.toString v) ^ " = ")
									) handle RuntimeError => ((Var.toString v) ^ " = ")
											| Not_found => ((Var.toString v) ^ " = "))
        						| Type_desc.Tvar _ => (
        							((Var.toString v) ^ " = " ^ (Int.toString (TheoremProver.get_int_value v model)) ^ "; ")
        							handle RuntimeError => ( 
        								((Var.toString v) ^ " = " ^ (Bool.toString (TheoremProver.get_bool_value v model)) ^ "; ")
        								handle RuntimeError => (
        									("len " ^ (Var.toString v) ^ " = " 
									 		^ (Int.toString (TheoremProver.get_int_value  (Var.fromString ("Array.length" ^ (Var.toString v) ^ "_")) model)) ^ "; ")
									 		handle RuntimeError => (
									 			((Var.toString v) ^ " = ")
									 		)
									 	)
									)
									)
								| Type_desc.Ttuple [] => "_;"
        						| _ => (print ("\nUnclear variable " ^ (Var.toString v) ^"\n"); "_;")
        				
        						
        				fun print_assignment_pat pat model =
        					let val str = ref "[ "
        					in 
        						CoreML.Pat.foreachVarwithType (pat, fn (v, ty) =>
        							str := (!str ^ (print_assignment v ty model))
        						);
        						str := (!str ^ " ]");
        						!str
        					end
        				fun print_assignment_exp exp model =  
        					let val str = ref "[ "
        					in
        						CoreML.Exp.foreachVarwithType (exp, fn (v, ty) =>
        							str := (!str ^ (print_assignment v ty model))
        						);
        						str := (!str ^ " ]");
        						!str
        					end
        			in
	        			print ("\nCounterexample path is shown below: @@@@@@@@@@@@@@@@@@@@@@@@ \n");
	        			List.foreach (cepath, fn (cpat, cexp, expclass) =>
						case expclass of 
							BackwardTraverse.ConditionalTrue => print ((CoreML.visitExp cexp) ^ " ==> " ^ (print_assignment_exp cexp model) ^"\n") 
							| BackwardTraverse.ConditionalFalse => print ((CoreML.visitExp cexp) ^ " ==> " ^ (print_assignment_exp cexp model) ^ "\n")
							| BackwardTraverse.Assignment => 
								print ((CoreML.Pat.visitPat cpat) ^ (print_assignment_pat cpat model) ^ " = " ^ (CoreML.visitExp cexp) ^ (print_assignment_exp cexp model) ^ "\n")
							| BackwardTraverse.Selection => 
								print ((CoreML.Pat.visitPat cpat) ^ (print_assignment_pat cpat model) ^ " = " ^ (CoreML.visitExp cexp) ^ (print_assignment_exp cexp model) ^ "\n")
						)
					end
        		
        		(* This funtion can or will serve many places.
        		 * 1. Some simply built-in function precondition need to be checked
        		 * 2. Some recored property will be omitted
        		 * 3. We could possibly move a constriant on a constructed variable to a functon nearby it. The reason is F f g x y = ... f x ... g y ...
        		 *    So f x and g y have correlations then the property setting for x from f could possibly be transited to g. In this case, you do not
        		 *    need to verfy the constraint on x any more.  
        		 *)
        		val arithops = ["+", "-", "*", "/", ">", ">=", "<=", "<", "<>_0", "=_0", "div"]
        		fun needNotCheck sri c =
        			(let val exp = Constraint.getExp sri c
        			in
        				case (Exp.node exp) of
        					Exp.App (e1, e2) =>
        						let val (funname, funpat) = Constraintgen.getFunctioinAppPat exp 
        							val funvar = Constraintgen.pat_var funpat
        						in
        							((Lightenv.mem funvar fenv) andalso 
											(List.exists (arithops, fn arithop => (String.compare (arithop, funname) = EQUAL))))			
        						end
        					| _ => false
        			end) handle RuntimeError => false
        		
        		fun verify' sri w = 
		        	let val (cnst, w') = Constraint.pop_worklist sri w
					in
						(case cnst of 
								SOME (c as (Ct.SubRef (env,g,r1, r2, funflag, recordIndex, con, conrecordIndex, SOME id)))  => 
									(* Note funflag can be used as functional subtyping indicator *)
									(print ("Verifying a constraint" ^ (Int.toString id) ^ " from the constraint heap with recordIndex of " 
										^ (Int.toString recordIndex) ^ " \n");
									if (HashTable.inDomain conpending id) then (print "This constraint is already embedded \n"; verify' sri w')
									else if (needNotCheck sri c) then (print "This constraint is or checked by another constraint \n"; verify' sri w')
									else (print "This constraint is not already embedded \n";
									let val _ = print ("constraint is " ^ (Constraint.pprint_ref NONE c) ^ "\n")
										val envpending = HashTable.mkTable (hash_fn o (Var.toString), Var.logic_equals) (37, Not_found)
										val refvarpending = HashTable.mkTable (hash_fn o (Var.toString), Var.logic_equals) (7, Not_found)
										val curfunname = Constraintgen.pat_var (#pat bcnst)	
										val funappsubs = (
														let val appe = (Constraint.getExp sri c) in
														case (Exp.node appe) of
														(Exp.App (e1, e2)) =>
															let val _ = print ("constriant is from exp " ^ (CoreML.visitExp appe) ^ "\n")
																val (_, funpat) = Constraintgen.getFunctioinAppPat appe
																val funname = Constraintgen.pat_var funpat
															in
																if (HashTable.inDomain bindingframe funpat 
																		andalso (not (Var.logic_equals (funname, curfunname)))
																		) then
																	let val f = HashTable.lookup bindingframe funpat
																	in (BackwardTraverse.genApplicationSubs appe true f) end
																else if (Lightenv.mem funname env) then
																	let val f = Lightenv.find funname env
																	in (BackwardTraverse.genApplicationSubs appe true f) end
																else 
																	[]
															end
														| _ => []
														end) handle RuntimeError => []
										(*val _  = print "\nfunapps show : \n";
										val _  = List.foreach (funappsubs, fn (a,b) => 
														  				print ("\n a " ^ (Var.toString a) ^ " b " ^ (Predicate.pprint_pexpr b) ^ "\n"));*)
										
										val qp2s = case r2 of 
											(sub2s, F.Qconst qs) => (
												print ("\nNNote: sub2s are " ^ (List.fold (sub2s, "", fn ((a, b), str) => 
													(str ^ " a is " ^ (Var.toString a) ^ " b is " ^ (Predicate.pprint_pexpr b)))) ^ "\n");
												(List.map (qs, fn q => 
													(SOME q,Ct.refinement_predicate sri sm Ct.qual_test_expr (sub2s@funappsubs,F.Qconst[q]) funflag 
																envpending conpending refvarpending polymatching_table ifb)))
											)
											| (sub2s, F.Qvar (k2, _)) =>
												(* Must transform (sm k2) into appropriate form in order to fit virtual (as parameter) fun call *)
												(* 1. get the fun call exp if funflag
												 * 2. get the real fun call parameters 
												 * 3. replace them into sm k2 with appropriate position
												 *)
												let val k2 = 
														if (HashTable.inDomain polymatching_table k2) then HashTable.lookup polymatching_table k2
														else k2
													val k2qs = sm k2 
													val exp = Constraint.getExp sri c
													(* You may want to remove all the higher order values *)
													val k2qs = if (HashTable.inDomain hov k2) then
																	List.firstN (k2qs, ((List.length k2qs)-1))
															   else k2qs
													(* You may also want to remove higher order constraint exerted on contructed variables because
													 * Our tool in theory forbid that. It comes from optimization. Just ignore it! *)
													(*val k2qs = case (Exp.node exp) of
														Exp.App (e1, e2) => (
															if (Type.isArrow (Exp.ty e2)) then
																k2qs
															else List.rev (List.removeAll (k2qs, fn (v1, v2, p) =>
																	Predicate.hasHovConstraint p
																))
														)
														| _ => k2qs
													*)
													val k2qs = case (Exp.node exp) of 
														  Exp.App (e1, e2) => 
														  	let val (funname, funpat) = Constraintgen.getFunctioinAppPat exp
														  	in
																if (HashTable.inDomain bindingframe funpat) then
																	(k2qs)
																else if (List.exists (built_ins, fn built_in => (String.compare (built_in, funname) = EQUAL))) then k2qs
																else  (* virtual fun call *)
																	let val actuals = ref []
																		val _ = Constraintgen.getFunctionAppParam exp actuals
																		(*val actuals = List.rev (!actuals)*)
																		val actuals = !actuals
																		(*val _ = print "actuals: \n"
																		val _ = List.foreach (actuals, fn ac => print ((Var.toString ac) ^ " "))*)
																	in
																		List.map (k2qs, fn (v1, v2, p) =>
																			let fun f var = 
																  				case HashTable.find parameterIndex_table var of 
														  							SOME varIndex => Predicate.PVar (List.nth (actuals, varIndex))
														  							| NONE => Predicate.PVar var
																  			in (v1, v2, Predicate.map_vars f p) end 
																		)
																	end 
															end
														| _ => k2qs
												in
												(List.map (k2qs, fn q => 
													(SOME q,Ct.refinement_predicate sri sm Ct.qual_test_expr (sub2s@funappsubs,F.Qconst[q])  
													funflag envpending conpending refvarpending polymatching_table ifb)
												))
												end
												handle RuntimeError => (
														(*print ("\n\n" ^ (Var.toString k2) ^ " is not a user function input but has no predicated attached" ^ 
																	" but maybe is a function input for embedded builtins \n\n");*)
														[]
														)	
										
										val (r1p, lhs) = Ct.implies_pred sri env g sm r1 funflag Ct.qual_test_expr 
											envpending conpending refvarpending polymatching_table ifb
										val lhs = if (recflag) then lhs else Predicate.apply_substs funappsubs lhs
										(* Also, you may want to add subsitution equality of formals and actuals for the e2 in (e1 e2)*)
									    (*val lhs = 
									    	(let val exp = Constraint.getExp sri c in
									    	case (Exp.node exp) of
									    	Exp.App (e1, e2) => 
									    		let val (_, funpat) = Constraintgen.getFunctioinAppPat exp 
										  		in
										  			if (HashTable.inDomain bindingframe (funpat)) then
										  				let val f = Lightenv.find (Constraintgen.pat_var funpat) env
										  					val subs = BackwardTraverse.genApplicationSubs exp true f
										  					val y = case (Exp.node e2) of
												  				Exp.Var (var, _) => Predicate.PVar (var ())
												  				| Exp.Record r => 
												  					let val plist = (Record.toVector r)
															  			val labeled_exprs = 
															  				QuickSort.sortVector (plist, (fn ((a, b), (a', b'))=> (Field.<= (a, a'))))	 
																		val sorted_exprs = 
																			((Vector.toList o (fn (a, b) => b)) (Vector.unzip labeled_exprs))
															  			val argr = (List.nth (sorted_exprs, recordIndex-1))
												  					in 
												  						case (Exp.node argr) of
												  							Exp.Var (var, _) => Predicate.PVar (var ()) 
												  							| _ => (print ("Nested record is not supported" ^ (CoreML.visitExp e2) ^ "\n"); 
												  									assertfalse ())
												  					end
												  				| Exp.Const f =>
																	(case (Type.toMyType (Exp.ty e2)) of
														  	  		  Type_desc.Tconstr (t, []) => 
														  	  		  	if (Tycon.isIntX t) then
														  	  		  		let val constval = f() in
														  	  		  			case constval of 
														  	  		  			     Const.IntInf n => (Predicate.PInt (IntInf.toInt n))
																			       | Const.Word n => (Predicate.PInt (WordX.toInt n))
																			       | _ => (print "toPredIntError\n"; assertfalse ())
														  	  		  		end  		
														  	  		  	else Predicate.PVar (Var.mk_ident "dummy")
														  	  		| _ => Predicate.PVar (Var.mk_ident "dummy"))
												  				| _ => (print ("Tool does support syntax like " ^ (CoreML.visitExp exp) ^ "\n"); 
												  								assertfalse ())
										  					val r = List.peek (subs, fn (v, x) => Predicate.logic_equals_pexp x y)
										  					val v = case r of SOME (v, _) => v | NONE => (print ("ill syntax given" 
										  																  ^ (CoreML.visitExp exp) ^ "\n"); assertfalse ())
										  				in
										  					Predicate.big_and ([lhs, Predicate.Atom (Predicate.PVar v, Predicate.Eq, y)])
										  				end
										  			else lhs
										  		end
									    	| _ => lhs
									    	end) handle RuntimeError => lhs*)
									    
									    val lhs = 
									    	(let val exp = Constraint.getExp sri c
									    	in 
									    		if funflag then lhs
									    		else 
									    			case (Exp.node exp) of
									    				Exp.App (_, e2) =>
									    					let val y = case (Exp.node e2) of
												  				Exp.Var (var, _) => (
												  					case (Type.toMyType (Exp.ty e2)) of
												  						Type_desc.Ttuple tlist =>
												  							if (recordIndex = 0) then Predicate.PVar (var ())
												  							else 
												  							let val tlist = QuickSort.sortList (tlist, fn (t1, t2) => 
												  								case (t1, t2) of
												  									(Type_desc.Tfield (ts1, _), Type_desc.Tfield (ts2, _)) => String.<= (ts1, ts2) 
												  									| _ => (print "Internal error occured\n"; assertfalse ()) 
												  								)
												  								val tslist = List.map (tlist, fn t => 
												  								case t of
												  									Type_desc.Tfield (ts, _) => ts
												  									| _ => (print "Internal error occured\n"; assertfalse ())
												  								)
												  								val fd = List.nth (tslist, recordIndex-1)
												  							in
												  								Predicate.Field (fd, Predicate.PVar (var ()))
												  							end	 
												  						| Type_desc.Tconstr (tyc, _) => 
												  							if (Tycon.equals (tyc, Tycon.list)) then Predicate.Field ("ele", Predicate.PVar (var ()))
												  							else Predicate.PVar (var ()) 
												  						| _ => Predicate.PVar (var ())
												  				)
												  				| Exp.Record r => 
												  					if (recordIndex > 0) then
												  					let val plist = (Record.toVector r)
															  			val labeled_exprs = 
															  				QuickSort.sortVector (plist, (fn ((a, b), (a', b'))=> (Field.<= (a, a'))))	 
																		val sorted_exprs = 
																			((Vector.toList o (fn (a, b) => b)) (Vector.unzip labeled_exprs))
																		val _ = print ("\nrecordIndex " ^ (Int.toString (recordIndex)) ^ "\n");
															  			val argr = (List.nth (sorted_exprs, recordIndex-1))
												  					in 
												  						case (Exp.node argr) of
												  							Exp.Var (var, _) => Predicate.PVar (var ()) 
												  							| _ => (print ("Nested record is not supported" ^ (CoreML.visitExp e2) ^ "\n"); 
												  									assertfalse ())
												  					end
												  					else (print "\nerror occured on record precondition checking\n"; assertfalse ())
												  				| (Exp.Con (c, targs)) => (case (Con.toString c) of
		      				  												"true" => Predicate.PInt 1
		      				  												| "false" => Predicate.PInt 0
		      				  												| _ => (print ("Unaccepted program syntax by the tool" ^ (CoreML.visitExp e2)); assertfalse ())
		      				  									)
												  				| _ => (print ("Don't add AA = " ^ (CoreML.visitExp exp) ^ "\n"); 
												  								assertfalse ())
												  			in
												  				Predicate.big_and ([lhs, Predicate.Atom (Ct.qual_test_expr, Predicate.Eq, y)])
												  			end
									    				| _ => lhs
									    	end) handle RuntimeError => lhs	
										(* add predicate of the form of AA = P1 x so we can compare higher order values *)
										val lhs = 
											(let val exp = Constraint.getExp sri c in
											if funflag then (
											case (Exp.node exp) of
											Exp.App (_, e2) => (
											if (HashTable.inDomain hov (getk2 r2)) then (	
												print "funflag in domain";
												let val (funvar, y, ty) = case (Exp.node e2) of
										  				Exp.Var (var, _) => (var (), Predicate.PVar (var ()), Exp.ty e2)
										  				| Exp.Record r => 
										  					let val plist = (Record.toVector r)
													  			val labeled_exprs = 
													  				QuickSort.sortVector (plist, (fn ((a, b), (a', b'))=> (Field.<= (a, a'))))	 
																val sorted_exprs = 
																	((Vector.toList o (fn (a, b) => b)) (Vector.unzip labeled_exprs))
													  			val argr = (List.nth (sorted_exprs, recordIndex-1))
										  					in 
										  						case (Exp.node argr) of
										  							Exp.Var (var, _) => (var (), Predicate.PVar (var ()), Exp.ty argr) 
										  							| _ => (print ("Nested record is not supported" ^ (CoreML.visitExp e2) ^ "\n"); 
										  									assertfalse ())
										  					end
										  				| _ => (print ("Tool does support syntax like " ^ (CoreML.visitExp exp) ^ "\n"); 
										  								assertfalse ())
													val pvs = ho_args_fromty (Type.toMyType ty) funvar
												in
													Predicate.big_and ([lhs, Predicate.Atom (Ct.qual_test_expr, Predicate.Eq, Predicate.FunApp ("P" ^ (Int.toString (List.length pvs)), y :: pvs))]) 
												end)
											else lhs
											)
											| _ => lhs)
											else lhs 
											end) handle RuntimeError => lhs 
										
										(*val _ = print ("\n\nthe left predicate is " ^ (Predicate.pprint lhs))*)
										(*val pred = Predicate.big_and (List.map (qp2s, fn(a,b) =>b))
										val _ = print ("\nthe predicate' is" ^ (Predicate.pprint pred) ^ "\n")
										val addingfunapps = Predicate.getAddFunApp pred
										val tpc = implies_tp lhs addingfunapps
									    val vr = tpc pred*)
									    
									    val tpc = implies_tp lhs (Predicate.getAddFunApp (Predicate.big_and (List.map (qp2s, fn (a, b) => b))))
									    val (unsatcore, vr) = List.fold (List.map (qp2s, fn (a, b) => b), ([], true), fn (pred, (uc, r)) => (
									    	print ("\nthe verification goal is" ^ (Predicate.pprint pred) ^ "\n");
									    	let (*val _ = print ("predicate size is " ^ (Int.toString (Predicate.size pred)) ^ "\n")*)
									    		val vr = tpc pred
									    		(*val _ = print ("vr is " ^ (Bool.toString vr) ^ "\n")*)
									     	in
									     		if (vr) then (uc, r)
									     		else (uc @ [pred], false)
									     	end)
									    )
									    val pred = Predicate.big_and unsatcore
									in
										(if vr then
											(TP.finish(); verify' sri w')
										else if funflag (*(isFunSubtypingCheck sri c)*) then (	
										 	(* Do not have to invoke testrune and backwalker module
										  	 * The reason is from this constraint, we only deal with the higher order feature
										  	 * There is just no need to track path at all
										  	 *)										  	
										  	(let 
										  		val _ = TP.finish()
										  		val t_start = Time.now ()
										  		val k2 = getk2 r2
										  		val k2qs = sm k2
										  		val k2qs = if (HashTable.inDomain hov k2) then
																	List.firstN (k2qs, ((List.length k2qs)-1))
															   else k2qs		   
												
												val sub2s = getSub2s r2
										  		(*val _ = List.foreach (sub2s, fn (v, p) => print ((Var.toString v) ^ " " ^ (Predicate.pprint_pexpr p)))*)
										  		val k2qs = List.map (k2qs, fn (v1, v2, p) => (v1, v2, Predicate.apply_substs sub2s p))
												
										  		val exp = Constraint.getExp sri c
										  	in
										  		case (Exp.node exp) of 
										  			Exp.App (e1, e2) => 
										  				let val (_, funpat) = Constraintgen.getFunctioinAppPat exp 
										  					val (_, pfunpat) = Constraintgen.getFunctioinAppPat e2
										  					(* if e2 is named function, it could be partial. We need to replace predicate vars with
													  		 * the partial value given to it.
													  		 *)
													  		
													  		val k2qs = 
													  			if (HashTable.inDomain bindingframe (funpat)) then
													  				let val f = Lightenv.find (Constraintgen.pat_var funpat) env
													  					val subs = BackwardTraverse.genApplicationSubs exp false f
													  				in
													  					List.map (k2qs, fn (v1, v2, p) => (v1, v2, Predicate.apply_substs subs p))
													  				end
													  			else k2qs
													  		
													  		val k1 = (case r1 of 
													  		  (_, F.Qvar (k1, _)) => (
													  		  	print ("Will Set a constraint for var " ^ (Var.toString k1) ^ " as " ^ 
													  		  		(List.fold (k2qs, "", fn (q, str) => (str ^ (Qualifier.pprint q) ^ "\n")))
													  		  	);
													  		  	HashTable.insert s (k1, k2qs);
													  		  	k1
													  		  )
													  		| _ => (print "Error: functional subtyping encounters ill form"; assertfalse ()))
													  	in	  	
													  		(* We make sure whether the constraint is propaged from funpat to pfunpat or the reverse *)
												  		  	if (HashTable.inDomain bindingframe (funpat)) then
												  		  		let val f= Lightenv.find (Constraintgen.pat_var funpat) env (*HashTable.lookup bindingframe (funpat)*)
												  		  		in
												  		  			if (Frame.queryExistenceFromArrowFrame f k1) then
												  		  				(* function funpat need to be refined *)
												  		  				(* Update k2qs with reasonable vars *)
												  		  				let (*val matching_subs = ref []*)
												  							(*val _ = BackwardTraverse.getFunctionParams exp matching_subs*)
												  							val subs = BackwardTraverse.genApplicationSubs exp true f
												  							(* Must transform it into appropriate form by index 
												  							 * iff pfunpat is higher order function
												  							 *)
												  							(*val _ = print ("\n0" ^ (List.fold (k2qs, "", fn (q, str) => (str ^ (Qualifier.pprint q) ^ "\n"))))
																	  		val k2qs = 
																	  			if (HashTable.inDomain bindingframe pfunpat) then 
																			  		let val fr = Lightenv.find (Constraintgen.pat_var pfunpat) env
																			  			val vars = Frame.funFramevars fr
																			  			val m_subs = List.mapi (vars, fn (index, var) => 
																			  				(var, Predicate.PVar (Var.fromString ("IV_" ^ (Int.toString index)))))
																			  		in
																			  			List.map (k2qs, fn (v1, v2, p) =>
																			  				(v1, v2, Predicate.apply_substs m_subs p)
																			  			)
																			  		end	
																	  		else k2qs *)
																	  		val _ = if (HashTable.inDomain bindingframe pfunpat) then 
																				  		let val fr = Lightenv.find (Constraintgen.pat_var pfunpat) env
																				  			val vars = Frame.funFramevars fr
																				  		in
																				  			List.foreachi (vars, fn (index, var) => 
																				  				HashTable.insert parameterIndex_table (var, index)
																				  			)
																				  		end
																				  	else ()
																	  		(*val _ = print ("\n1" ^ (List.fold (k2qs, "", fn (q, str) => (str ^ (Qualifier.pprint q) ^ "\n"))))*)
																	  		(* You may want to simplify the predicate using funpat parameter *)
													  		  				val k2qs = List.map (k2qs, fn (v1, v2, p) => (
																	  			(*let fun f var = 
																	  					let val varx = List.peek (subs, fn (a, b) =>
																	  							case b of 
																	  								Predicate.PVar b => Var.logic_equals (b, var)
																	  								| _ => false
																	  						)
																	  						val varx = case varx of
																	  							SOME (a, b) => a
																	  							| NONE => var
																	  					in
																	  						Predicate.PVar varx
																	  					end
																	  			in (v1, v2, Predicate.map_vars f p) end *)
																	  			(*List.foreach (subs, fn (a,b) => 
																	  				print ("\n a " ^ (Var.toString a) ^ " b " ^ (Predicate.pprint_pexpr b) ^ "\n"));*)
																	  			(v1, v2, List.fold (subs, p, fn ((a, b), p') =>
																	  				case b of 
																	  					Predicate.PInt _ => p' 
																	  					| _ => Predicate.subst2 (Predicate.PVar a) b p'
																	  			)))
																	  		)
																	  		(*val _ = print ("\n2" ^ List.fold (k2qs, "", fn (q, str) => (str ^ (Qualifier.pprint q) ^ "\n")))
																	  		val _ = print " Here3? "*)
																  		(* End updating k2qs*)
												  		  					val k1' = if (HashTable.inDomain polymatching_table k1) then 
												  		  									SOME (HashTable.lookup polymatching_table k1)
												  		  							  else NONE 
												  		  				in
												  		  					HashTable.insert s (k1, k2qs);
												  		  					case k1' of
												  		  						SOME k1' => (
														  		  					HashTable.insert s (k1', k2qs);
														  		  					(*(false, SOME funpat, SOME ((k1, k2qs)::kls)) *)
														  		  					incr_t_iteration t_start;
														  		  					(false, SOME funpat, (SOME [(k1', k2qs)]), SOME id, SOME exp)
														  		  				)
														  		  				| NONE => (
														  		  					incr_t_iteration t_start;
														  		  					(false, SOME funpat, (SOME [(k1, k2qs)]), SOME id, SOME exp)
														  		  				)
												  		  				end
												  		  			else if (HashTable.inDomain bindingframe (pfunpat)) then
												  		  				let val pf = Lightenv.find (Constraintgen.pat_var pfunpat) env (*HashTable.lookup bindingframe (pfunpat)*)
												  		  				in
												  		  					if (Frame.queryExistenceFromArrowFrame pf k1) then
														  		  				(* function pfunpat need to be refined, try not propagate higher order value *)
														  		  				(*if ((List.length k2qs) > 1) then
															  		  				let val k2qs = List.firstN (k2qs, ((List.length k2qs)-1))
															  		  					val _ = HashTable.insert s (k1, k2qs)
															  		  				in
															  		  					(false, SOME pfunpat, SOME (k1, k2qs))
															  		  				end
														  		  				else (* The failure is caused just because of higher order value *)
														  		  					verify' sri w' 
														  		  				*)
														  		  				
														  		  				let val k1' = if (HashTable.inDomain polymatching_table k1) then
														  		  									SOME (HashTable.lookup polymatching_table k1)
														  		  							  else NONE
														  		  				in
														  		  					case k1' of
														  		  						SOME k1' => (
														  		  							HashTable.insert s (k1', k2qs);
														  		  							incr_t_iteration t_start;
														  		  							(false, SOME pfunpat, SOME [(k1', k2qs)], SOME id, SOME exp) 
														  		  							)
														  		  						| NONE => (
														  		  							incr_t_iteration t_start;
														  		  							(false, SOME pfunpat, SOME [(k1, k2qs)], SOME id, SOME exp)
														  		  						)
														  		  				end
														  		  			else  
														  		  				(print ("\ntheory error for subtyping\n"); assertfalse ())
														  		  		end
														  		  	(* partial application may also tend to be a concrete function *)
												  		  			else (
												  		  				incr_t_iteration t_start;
												  		  				(false, NONE, SOME [(k1, k2qs)], SOME id, SOME exp)
												  		  			)
												  		  		end
												  		  	else if (HashTable.inDomain bindingframe (pfunpat)) then
												  		  		let val pf = Lightenv.find (Constraintgen.pat_var pfunpat) env (*HashTable.lookup bindingframe (pfunpat)*)
												  		  		in
												  		  			if (Frame.queryExistenceFromArrowFrame pf k1) then
												  		  				(* function pfunpat need to be refined, try not propagate higher order value *)
												  		  				(*if ((List.length k2qs) > 1) then
													  		  				let val k2qs = List.firstN (k2qs, ((List.length k2qs)-1))
													  		  					val _ = HashTable.insert s (k1, k2qs)
													  		  				in
													  		  					(false, SOME pfunpat, SOME (k1, k2qs), SOME id, SOME exp)
															  		  		end
														  		  		else (* The failure is caused just because of higher order value *)
														  		  			verify' sri w'
														  		  		*)
														  		  		let val k1' = if (HashTable.inDomain polymatching_table k1) then
														  		  							SOME (HashTable.lookup polymatching_table k1)
														  		  					  else NONE
														  		  		in
														  		  			case k1' of
														  		  				SOME k1' => (
														  		  					HashTable.insert s (k1', k2qs);
														  		  					incr_t_iteration t_start;
														  		  					(false, SOME pfunpat, SOME [(k1', k2qs)], SOME id, SOME exp)
														  		  					)
														  		  				| NONE => (
														  		  					incr_t_iteration t_start;
														  		  					(false, SOME pfunpat, SOME [(k1, k2qs)], SOME id, SOME exp)
														  		  				)
														  		  		end
														  		  	else (
														  		  		incr_t_iteration t_start;
														  		  		(false, NONE, SOME [(k1, k2qs)], SOME id, SOME exp)
														  		  	)
												  		  		end
												  		  	(* partial application may also tend to be a concrete function *)
												  		  	else (
												  		  		incr_t_iteration t_start;
												  		  		(false, NONE, SOME [(k1, k2qs)], SOME id, SOME exp)		
												  		  	)								  				
										  				end
										  			| _ => ((* We have already set it!! *)
										  				print ("Directly propagate for " ^ (CoreML.visitExp exp));
										  				(case r1 of 
													  		  (_, F.Qvar (k1, _)) => (
													  		  	print ("Will Set a constraint for var " ^ (Var.toString k1) ^ " as " ^ 
													  		  		(List.fold (k2qs, "", fn (q, str) => (str ^ (Qualifier.pprint q) ^ "\n")))
													  		  	);
													  		  	HashTable.insert s (k1, k2qs);
													  		  	let val ks = Constraint.getCurriedKs sri k1
																in
																	List.foreach (ks, fn k => (print ("also setting for " ^ (Var.toString k) ^ "\n"); HashTable.insert s (k, k2qs)))
																end
													  		  )
													  		| _ => (print "Error: functional subtyping encounters ill form 2"; assertfalse ()))
										  				; incr_t_iteration t_start
										  				; verify' sri w' 
										  			)
										  	end) handle RuntimeError => 
										  			(print ("\n\n***********Internal Error for fun param: ***********\n\n"); verify' sri w'))
										else (
											(* Have to invoke testrun and backwalker module 
											 * step1 : get abstract path
											 * step2 : test run to get concrete path
											 * step3 : compare abstract path and path
											 * step4 : backwalk to add new precondition or postcondition 
											 *)
											let val t_start = Time.now ()
												val exp = Constraint.getExp sri c
												val cfname = Constraintgen.pat_var (#pat bcnst)	
												val _ = print ("The constraint is from exp" ^ (CoreML.visitExp exp) ^ "\n")
												
												(*val _ = print ("the predicate for path up is: " ^ (Predicate.pprint pred) ^ "\n")*)
												val model = TheoremProver.get_model ()
												(* Refine the predicate that should be used in path up *)
												(*val predlist = Predicate.andPredicateList pred
												val pred = if ((List.length predlist) > 1) then
																let val predlist = Common.map_partial 
																	(fn pi => if (TheoremProver.evaluate_in_model model pi) then NONE else SOME pi) 
																	predlist
																in Predicate.big_and predlist end
														   else pred*)
												(*val _ = print ("the predicate for path up is indeed: " ^ (Predicate.pprint pred))*)
												
												
												fun makeConPredicate pexp = 
													case con of 
														SOME con => (* constructor *) (
															Predicate.Proj (conrecordIndex, Predicate.Field (Con.toString con, pexp))
															)
														| NONE => pexp 

												val (pred, post, fr, exp, force_convergence_flag) = case (Exp.node exp) of
													Exp.App (e1, e2) => 
														let val (funname, funpat) = Constraintgen.getFunctioinAppPat exp
													    in
													    	if (String.compare (funname, "assert") = EQUAL) then
													  	    	(* The verfication for assertion *)
													  	    	let val r = 
													  	    		case pred of 
													  	    			Predicate.Atom (tagf, Predicate.Eq, (Predicate.PInt 1)) =>
													  	    				List.peek (paths, fn (_, pexpr, pred, assertflag) => 
													  	    					assertflag andalso P.logic_equals_pexp tagf pexpr)
													  	    			| _ => assertfalse ()
													  	    		val pred = 
													  	    		case r of 
													  	    			SOME (_, _, pred, _) => pred
													  	    			| _ => assertfalse ()
													  	    		val funvar = Constraintgen.pat_var funpat
													  	    	in
													  	    		(pred, false, SOME (funvar, Frame.Fvar((Var.mk_ident "dummy"), Frame.empty_refinement)), 
													  	    		exp, false)
													  	    	end
													  		else (* The verification for satisfying precondition *)
													  			let fun get_fr () = 
													  					let val (funname, funpat) = Constraintgen.getFunctioinAppPat exp
											  								val funvar = Constraintgen.pat_var funpat
																			val fr = if (HashTable.inDomain bindingframe funpat) then
													  							HashTable.lookup bindingframe funpat
													  						else if (Lightenv.mem funvar env) then
													  							Lightenv.find funvar env
													  						else if (Lightenv.mem funvar fenv) then
													  							Lightenv.find funvar fenv
													  						else if (HashTable.inDomain envpending funvar) then
													  							HashTable.lookup envpending funvar
													  						else
													  							(print ("Error: cannot get a frame for " ^ funname); assertfalse ())
													  					in
													  						(funvar, fr)
													  					end			
													  															  						
													  				val (funvar, fr) = get_fr ()
													  					
																	val argument = case (Exp.node e2) of 
																		  Exp.Record r => 
																		  	let val plist = (Record.toVector r)
																		  		val labeled_exprs = 
																		  		QuickSort.sortVector (plist, (fn ((a, b), (a', b'))=> (Field.<= (a, a'))))	 
		  	  																	val sorted_exprs = 
		  	  																	((Vector.toList o (fn (a, b) => b)) (Vector.unzip labeled_exprs))
																		  		val _ = print ("\nIs error here?\n" ^ (CoreML.visitExp e2) ^ " : " ^
																		  		(Int.toString recordIndex))
																		  		val unitflag = ref false
																		  		val argr = if ((List.length sorted_exprs) > 0) then 
																		  						(List.nth (sorted_exprs, recordIndex-1))
																		  				   else (unitflag := true; e2) (* means unit type *)
																		  	in
																		  		case (Exp.node argr) of 
																		  			Exp.Var (varf, vart) => Predicate.PVar (varf ())
																		  			| Exp.App _ => Constraintgen.expression_to_pexpr argr
																		  			| Exp.Const _ => Constraintgen.expression_to_pexpr argr
																		  			| _ => 
																		  				if (!unitflag) then
																		  					Predicate.PVar (Var.mk_ident "")
																		  				else
																				  			(print ("Unaccepted nested record syntax" ^ 
																				  			(CoreML.visitExp argr)); assertfalse ())
																		  	end
																		| Exp.Var (varf, vart) => (
																				let val mty = Type.toMyType (Exp.ty e2)
																					(*val _ = print "\n---Tool comes hrere---\n"
																					val _ = print (case con of SOME con => "\ncon\n" | NONE => "\nnone con\n")
																					val _ = print ("\nrecordIndex is " ^ (Int.toString recordIndex) ^ "\n")
																					val _ = print ("mty is " ^ (CoreML.visitType (Exp.ty e2)) ^ "\n")*)
																				in
																					case mty of 
																						Type_desc.Ttuple ts =>
																							if (recordIndex > 0) then 
																								let val t = List.nth (ts, recordIndex-1)
																								in
																									case t of 
																										Type_desc.Tfield (n, _) => 
																										Predicate.Field (n, Predicate.PVar (varf ()))
																										| _ => assertfalse ()
																								end
																							else makeConPredicate (Predicate.PVar (varf ()))
																						| Type_desc.Tconstr (tyc, _) =>
																							if (Tycon.equals (tyc, Tycon.list)) then Predicate.Field ("ele", Predicate.PVar (varf ()))
																							else makeConPredicate (Predicate.PVar (varf ())) 
																						| _ => makeConPredicate (Predicate.PVar (varf ()))
																				end
																			)
																		| Exp.Const f =>
																			(case (Type.toMyType (Exp.ty e2)) of
																  	  		  Type_desc.Tconstr (t, []) => 
																  	  		  	if (Tycon.isIntX t) then
																  	  		  		let val constval = f() in
																  	  		  			case constval of 
																  	  		  			     Const.IntInf n => (Predicate.PInt (IntInf.toInt n))
																					       | Const.Word n => (Predicate.PInt (WordX.toInt n))
																					       | _ => (print "toPredIntError\n"; assertfalse ())
																  	  		  		end  		
																  	  		  	else Predicate.PVar (Var.mk_ident "dummy")
																  	  		| _ => Predicate.PVar (Var.mk_ident "dummy"))
																  	  	| Exp.App _ => Constraintgen.expression_to_pexpr e2
																  	  	| (Exp.Con (c, targs)) => (case (Con.toString c) of
		      				  												"true" => Predicate.PInt 1
		      				  												| "false" => Predicate.PInt 0
		      				  												| _ => (print ("Unaccepted program syntax by the tool" ^ (CoreML.visitExp e2) ^ " with type " 
													  										^ (CoreML.visitType (Exp.ty e2))); assertfalse ())
		      				  											)
													  					| _ => (print ("Unaccepted program syntax by the tool" ^ (CoreML.visitExp e2) ^ " with type " 
													  										^ (CoreML.visitType (Exp.ty e2))); 
													  					assertfalse ())										  				
													  			in
													  				let val rec_flag =
													  					Var.logic_equals (cfname, Constraintgen.pat_var funpat)
													  					val force_convergence_flag = ref false
													  					val cid = Constraint.get_ref_id c
													  					val pred = 
													  					if (rec_flag) then (
														  					let val regular_pred = Predicate.subst argument Ct.qual_test_var pred
											  								in		
															  					if (HashTable.inDomain force_convergence_table cid) then
															  						(* If the predicate size exceeds the predefined threshold, then stop
															  						 * and use the a copy of the predicate in force_convergence_table to 
															  						 * force the function verification converge. 
															  						 *)
															  						 
															  						let val (e,a,fp,msi,count) = HashTable.lookup force_convergence_table cid
															  						in
															  							if (count > 3) then 
															  								(print ("\ndivergence of count" ^ (Int.toString count) ^ "\n"); 
															  								(force_convergence_flag := true); fp)
															  							else (
															  								HashTable.insert force_convergence_table (cid, (e,a,fp,msi,count+1));
															  								regular_pred
															  							)
															  						end 
															  					else 
															  						(* Let the constraint be checked. 
															  						 * Hopefully it will converge but it may not be 
															  						 *)
															  						let val force_convergence_pred = 
															  								(* Substitute qual_test_var with formals *)
												  											(* But only if the predicate refers to freevariables can we do that *)
													  										let val subs = BackwardTraverse.genApplicationSubs exp true fr
													  											val r = List.peek (subs, 
													  													fn (v, x) => Predicate.logic_equals_pexp x argument
										  																)
										  														val v = case r of SOME (v, _) => v | NONE => 
										  																(print ("ill syntax given" 
										  																  ^ (CoreML.visitExp exp) ^ "\n"); assertfalse ())
													  										in Predicate.subst (Predicate.PVar v) Ct.qual_test_var pred end
													  									(* Make a copy of current solution *)
													  									val msi = HashTable.copy s
													  									val _ = HashTable.insert force_convergence_table 
													  												(cid, (exp, argument, force_convergence_pred, msi, 0))
													  								in regular_pred end
														  					end	
													  					)
													  					else (
													  						Predicate.subst argument Ct.qual_test_var pred
													  					)
													  				in
													  					(pred, false, SOME (funvar, fr), exp, (!force_convergence_flag))
													  				end
													  			end
													  	end 
													| Exp.Var (varf, vart) => (
														case r2 of 
															(sub2s, F.Qvar (k2, _)) => (* still precondition which is set by tool *)
															if (HashTable.inDomain k_precondition_table k2) then
																let val (fr, exp) = HashTable.lookup k_precondition_table k2
																	val mty = Type.toMyType (Exp.ty exp)
																	val pe = case mty of 
																		Type_desc.Ttuple ts =>
																			let val t = List.nth (ts, recordIndex-1)
																			in
																				case t of 
																					Type_desc.Tfield (n, _) => 
																					Predicate.Field (n, Predicate.PVar (varf ()))
																					| _ => assertfalse ()
																			end
																		| _ => makeConPredicate (Predicate.PVar (varf ()))	
																	val pred = Predicate.subst pe Ct.qual_test_var pred
																in 															
																	(pred, false, SOME fr, exp, false) 
																end
															else (print "Unknown var constraint"; assertfalse ())
															| _ => (print "Unknown var constraint"; assertfalse ())
													  )
													| Exp.Record r => (
														case r2 of
															(sub2s, F.Qvar (k2, _)) => (* still precondition which is set by tool *)
															if (HashTable.inDomain k_precondition_table k2) then 			
																let val (fr, exp) = HashTable.lookup k_precondition_table k2
																	val plist = (Vector.toList o (fn (a, b) => b)) (Vector.unzip (Record.toVector r)) 
																	val argument = case r1 of 
																		([], F.Qconst [(v1, v2, p)]) => (
																			case p of 
													  					  		Predicate.Atom (_, Predicate.Eq, v) => v
													  							| _ => (print ("Unaccepted program syntax by the tool" ^ 
																						(CoreML.visitExp exp)); assertfalse ())
																			)
																		| _ => (print ("Unaccepted program syntax by the tool" ^ 
																				(CoreML.visitExp exp)); assertfalse ())
																	val pred = Predicate.subst argument Ct.qual_test_var pred
																in
																	(pred, false, SOME fr, exp, false)
																end
															else (print "Unknown record constraint"; assertfalse ())
															| _ => (print "Unknown record constraint"; assertfalse ())
													  )
													| _ => (* The verification for function postcondition *)
														let val pe = 
															if (recordIndex = 0) then
																case con of 
																NONE =>
																Predicate.subst (Predicate.PVar (Var.fromString "dummy")) 
																Ct.qual_test_var pred
																| SOME con => 
																Predicate.subst (Predicate.Proj (conrecordIndex, Predicate.Field (Con.toString con,
																Predicate.PVar (Var.fromString "dummy"))))
																Ct.qual_test_var pred
															else 
																case con of
																NONE =>
																Predicate.subst (Predicate.Field (Int.toString recordIndex, 
																				(Predicate.PVar (Var.fromString "dummy")))) 
																Ct.qual_test_var pred
																| SOME con =>
																Predicate.subst (Predicate.Proj (conrecordIndex, Predicate.Field (Con.toString con, 
																Predicate.Field (Int.toString recordIndex, 
																				(Predicate.PVar (Var.fromString "dummy"))))))
																Ct.qual_test_var pred
														in
															(pe, true, NONE, exp, false)
														end
												val curfunvar = Constraintgen.pat_var (#pat bcnst)
												val curpaths = List.keepAllMap (paths, fn (bpat, path, pred, assertflag) =>
													if (Var.logic_equals ((Constraintgen.pat_var bpat), curfunvar)) then SOME (path, pred, assertflag)
													else NONE
												)
												
												(*val _ = print "\nobtained path for this function\n"
												val _ = List.foreach (curpaths, fn (path, pred, assertflag) => 
									    			print ( 
									    				(Predicate.compact_pprint_pexpr path) ^ " " ^ (Predicate.pprint pred) ^ " " ^
									    				(Bool.toString assertflag) ^ "\n"))*)
									    		
												val curpaths = QuickSort.sortList (curpaths, fn ((path1,_,assertflag1), (path2,_,assertflag2)) =>
													let val pathindex1 = Predicate.compact_pprint_pexpr path1
														val pathindex2 = Predicate.compact_pprint_pexpr path2
														val pathindex1size = String.length pathindex1
														val pathindex2size = String.length pathindex2
														val pathindex1 = 
															if (assertflag1) then String.substring (pathindex1, 17, pathindex1size-17)
															else if (String.hasPrefix (pathindex1, {prefix = "__tag"})) then String.substring (pathindex1, 10, pathindex1size-10)
															else String.substring (pathindex1, 5, pathindex1size-5)
														val pathindex2 = 
															if (assertflag2) then String.substring (pathindex2, 17, pathindex2size-17)
															else if (String.hasPrefix (pathindex2, {prefix = "__tag"})) then String.substring (pathindex2, 10, pathindex2size-10)
															else String.substring (pathindex2, 5, pathindex2size-5)
														val pathindex1 = Common.string_to_int pathindex1
														val pathindex2 = Common.string_to_int pathindex2
													in
														(pathindex1 < pathindex2)
													end
												)
									    		val _ = List.foreach (curpaths, fn (path, pred, assertflag) => 
									    			print ( 
									    				(Predicate.compact_pprint_pexpr path) ^ " " ^ (Predicate.pprint pred) ^ " " ^
									    				(Bool.toString assertflag) ^ "\n"))
												
												(* abstractpath could be empty list if not branches exist *)
												val abstractpath = TheoremProver.getAbstractPath curpaths model
												
												(* For the predicate given to test, it is better to not include higher order values.
												 * Orelse the program generated will have obstacles to deal with predicates referring higher order values
												 * So we can replace higher order values with a simple var
												 * However, the predicate for path up should still use the predicate with higher order values
												 * Discarding ...
												 *)
												(*val concretepath = TestRun.compileExecute 
																	sri
																	decs
																	(#pat bcnst) (* function (var, ty) *) 
																	(#exp bcnst) (* function expression *)
																	(#fr bcnst)  (* function frame *)
																	post
																	(*(if (funflag) then (Predicate.Not Predicate.True) else pred)
																	 *should avoid higher order value*)
																	((fn (a, b) => a) (Predicate.compressHOFunTermToVar pred))
																	recflag
																	fenv
																	model
																	fr
																	sm
																	freevars
        															k_fun_pathup_precondition_table
																	
												val _ = print "Have a look at abstractpath: \n"
												val _ = List.foreach (abstractpath, fn (ap, pred) => 
													(print ("ap: " ^ ap); print ("pred: " ^ Predicate.pprint pred);
													 print "\n")
												)
												val _ = print "Have a look at concretepath: \n"
												val _ = List.foreach (concretepath, fn cp =>
													(print ("cp: " ^ cp); print "\n")
												)
												
												val abstractpath_len = List.length abstractpath
												val concretepath_len = List.length concretepath
												
												(* Analyzing abstract path and concrete path *)
												fun pickFromPath abstractpath concretepath index = 
														if (index >= concretepath_len) then 
															(print "\nconcrete index out of bound"; assertfalse ())
														else if (index >= abstractpath_len) then (
															(* which means the end of abstract path *)
															let val cp = List.nth (concretepath, index)
																val len = ((String.length cp)-1)
																val cp = String.substring (cp, 0, len)
															in
																if (String.equals (cp, "unsucc")) then (* seeking precondition *) 
																	(~1, pred)
																else if (String.equals (cp, "succ")) then (* seeking postcondition *) 
																	(index, pred)
																else (print "\nError concretepath"; assertfalse ())
															end
														)
														else (
															let val (ap, pred) = List.nth (abstractpath, index)
																val cp = List.nth (concretepath, index)
																val len = ((String.length cp)-1)
															in
																if (String.equals (ap, (String.substring (cp, 0, len)))) then
																	pickFromPath abstractpath concretepath (index + 1)
																else (* seeking postcondition *) 
																	case cp of
																		"true" => (index, pred)
																		| "false" => (index, Predicate.Not pred)
																		| _ => (print "Internal Error"; assertfalse ())
															end
														) 
																		   
												val _ = print "Have a look at abstractpath again: \n"
												val _ = List.foreach (abstractpath, fn (ap, pred) => 
													(print ("ap: " ^ ap); print ("pred: " ^ Predicate.pprint pred);
													 print "\n")
												)
												val _ = print "Have a look at concretepath again: \n"
												val _ = List.foreach (concretepath, fn cp =>
													(print ("cp: " ^ cp); print "\n")
												)
												Discarded.*)
												
												(*val _ = print "Have a look at abstractpath: \n"
												val _ = List.foreach (abstractpath, fn (ap, pred) => 
													print ("select path: " ^ (Int.toString ap) ^ " under pred: " ^ (Predicate.pprint pred) ^ "\n")
												)*)
												(*val _ = TP.finish()*)
													
												(*val (index, pred) = pickFromPath abstractpath concretepath 0
												
												val _ = print ("***********************************" ^
													"divergingpoint is " ^ (Int.toString index) ^ "\n")	
												val _ = print ("***********************************" ^
													"divergingPred is " ^ (Predicate.pprint pred) ^ "\n")
												*)
												val _ = print ("Now generating priciser abstractions with  fcflag as " ^ 
														(Bool.toString (force_convergence_flag)) ^ "\n")				   
											in
												(*if (funflag) then ( (* funflag means generating functional precondition *)
													let val k2qs = sm (getk2 r2)
													in 
														(case r1 of 
												  		  (_, F.Qvar (k1, _)) => (
												  		  	print ("Seting a constraint for var " ^ (Var.toString k1) ^ " as " ^ 
												  		  		(List.fold (k2qs, "", fn (q, str) => (str ^ (Qualifier.pprint q) ^ "\n")))
												  		  	);
												  		  	HashTable.insert s (k1, k2qs);
												  		  	(* Set for chainlist of k1 *)
												  		  	let val ks = Constraint.getRelatedKs sri k1
												  		  	in List.foreach (ks, fn k => HashTable.insert s (k, k2qs)) end
												  		  )
												  		| _ => (print "Error: functional subtyping encounters ill form"; assertfalse ()))
													end
												) else ();*)
												(*if (index = ~1) then  abstract and concrete path are identical *)
													(let val (k, kqs, pat, cepath) = BackwardTraverse.precondition 
																				pred 
																				exp 
																				(#exp bcnst) 
																				(*concretepath*) ((List.map (abstractpath, fn (a, b) =>a)))
																				bindingframe 
																				fenv 
																				s 
																				freevars
																				totalvars 
																				recflag 
																				(#fr bcnst) 
																				envpending 
																				sri 
																				funflag 
																				k_fun_pathup_precondition_table 
																				env
																				force_convergence_flag 						
																				
														(* We have model and cepath and can report the counter example path *)						
														val _ = print_ce cepath model
														val _ = TP.finish()						
														(*val _ = if (force_convergence_flag) then  
																	let val k = getk2 r2
																		val ks = Constraint.getCurriedKs sri k
																	in
																		(*HashTable.insert s (k, []);
																		print "forcing convergence, removing constraints on previous ks for \n";*)
																		List.foreach (ks, fn k => 
																			(*(HashTable.insert s (k, []);*)
																			if HashTable.inDomain k_precondition_table k then
																				ignore (HashTable.remove k_precondition_table k)
																			else ())
																		)
																		(*List.foreach (ks, fn k => print ((Var.toString k) ^ " "));
																		print "\nall above constraint on ks removed."*)
																	end
																else ()*)
													in
														case pat of 
															SOME pat => (* Need to assume a postcondition instead *)
																(* Howeever, maybe not enough, caz you have to consider polymorphic funtion type *)
																if (HashTable.inDomain polymatching_table k) then 
																	let val k' = HashTable.lookup polymatching_table k
																	in
																		HashTable.insert s (k', kqs);
																		incr_t_iteration t_start;
																		(false, SOME pat, SOME [(k', kqs)], SOME id, SOME exp)
																	end
																else (
																	incr_t_iteration t_start;
																	(false, SOME pat, SOME [(k, kqs)], SOME id, SOME exp)
																)
															| NONE => ( (* We can generate preconditions now *)
															 	case fr of 
															 		  SOME fr => 
															 			HashTable.insert k_precondition_table (k, (fr, exp))
															 		| _ => ();
															 	(*print ("\nforce_convergen_flag is " ^ (Bool.toString force_convergence_flag) ^ "\n");*)
															 	if (force_convergence_flag) then raise BackwardTraverse.Not_Converge else ();
															 	(*print "Back from precondition generation !\nFor recrusive function reverifying more\n";*)
															 	let val ks = (k :: (Constraint.getCurriedKs sri k))
															 		(*val cw = List.fold (ks, w, fn (k, w) => 
																 		if (HashTable.inDomain (#rhs_km sri) k) then
																 			let val css = HashTable.lookup (#rhs_km sri) k
																		 		val css = Common.map_partial (fn ci =>
																		 			if (ci = id) then NONE
																		 			else (
																		 				let val cs = Constraint.get_ref_constraint sri ci
																			 			in
																			 				case (Exp.node (Constraint.getExp sri cs)) of
																			 					Exp.App _ => SOME cs
																			 					| _ => NONE
																			 			end handle RuntimeError => NONE
																		 			)
																		 		) css 
																			in Constraint.push_worklist sri w css end
																 		else w
															 		)*)
															 		val cw = w
															 		val _ = incr_t_iteration t_start
																in verify' sri cw end (* still w, caz we want to verify all of the possible path leading to it *)
															)
													end) handle BackwardTraverse.Not_Converge => (
														(* Recover to the original qualifiers that causes divergence *)
														(*let val _ = print "\nCatch the throw event\n"
															val cid = Constraint.get_ref_id c
															val (_,_,_,msi,_) = HashTable.remove force_convergence_table cid
														in
															(*s <-- msi*)
															HashTable.modifyi (fn (k, _) => 
																HashTable.lookup msi k
															) s
														end;*)
														List.push (non_convergence_table, (#pat bcnst, (CoreML.visitExp exp))); 
														incr_t_iteration t_start;
														verify' sri w'
													)									
											end 	
										))
									end))
								| NONE => (
									print "\nconstraints are exaushted already\n\n";
									(* Print out the inferred settings to the back up table which is back_s. But only for current verifying procedure. 
									 * To some extends, we can claim that weakest preconditions are recorded in the back_s *) 
									if (procedureflag) then
										case (#fr bcnst) of 
											Frame.Farrow _ =>
												let val kks = Frame.arrowframe_parameter_refinement_vars (#fr bcnst)
													val kset = HashTable.mkTable (hash_fn o Var.toString, Var.logic_equals) (17, Not_found)
													val _ = List.foreach (kks, fn k => (
														HashTable.insert kset (k, ());
														List.foreach (Constraint.getCurriedKs sri k, fn k' => 
															HashTable.insert kset (k', ())
														))
													)
												in
													HashTable.modifyi (fn (k, _) =>
														if (HashTable.inDomain kset k) then HashTable.lookup s k
														else HashTable.lookup back_s k  
													) back_s
												end
											| _ => ()
									else (
										(* Intermediate refinement inferred*)
										let val ks = case (#fr bcnst) of
											Frame.Farrow _ => Frame.arrowframe_refinement_vars (#fr bcnst)
											| _ => Frame.refinement_vars (#fr bcnst)
										in
											List.foreach (ks, fn k =>
						  						if (HashTable.inDomain s k) then
						  							List.foreach (HashTable.lookup s k, fn (_, _, p) =>
														let val plen = Predicate.size p
														in
															if (plen > (!intermediate_max_refinement_len)) then intermediate_max_refinement_len := plen
															else ()
															; intermediate_nb_refinement := (!intermediate_nb_refinement) + 1
														end
													)  
						  						else ()
						  					)
										end
									); 
									(true, NONE, NONE, NONE, NONE)
								)
								| _ => (print "ill constraint from modular heap; we currently discard it"; 
										case cnst of
											SOME c => print (Constraint.pprint_ref NONE c)
											| _ => print "NONE constraint" 
										;
										verify' sri w'))  	
					end
				in
					verify' sri w
				end
        
	end