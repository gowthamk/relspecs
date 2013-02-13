(*
 * This file is the backtraverse of sml expression according to a path
 * Author : He Zhu
 * Affiliation: CS@Purdue
 *)
 
structure BackwardTraverse =
	struct
	
		open CoreML
		open Frame
		open Common
		datatype exptype = ConditionalTrue | ConditionalFalse | Assignment | Selection
		
		val hash_fn = HashString.hashString
		
		val dummypat = Pat.var (Var.fromString "dummy", Type.var(Tyvar.newNoname {equality = false}))
		
		(*
		 * Simply analyze the function frame and generate the asserts and assumes for the function
		 *)	
		fun anlyFrowRefVar pat subs fr s = 
			let fun assertSet pat fr = 
					let val varfrs = Frame.bind pat fr
						val preds = Common.map_partial (fn (var, frame) => 
				  			case frame of 
				  				Fconstr (_, _, (subs, Qvar (k, _))) => 
				  					let val quals = (HashTable.lookup s k)
				  						val unsubst = List.map (quals, Qualifier.apply (Predicate.PVar var))
				  						val preds = List.map (unsubst, (Predicate.apply_substs subs))
				  					in SOME preds end
				  				| Fconstr (_, _, (subs, Qconst quals)) =>
				  					let val unsubst = List.map (quals, Qualifier.apply (Predicate.PVar var))
				  						val preds = List.map (unsubst, (Predicate.apply_substs subs))
				  					in SOME preds end
				  				| Farrow _ => 
				  					let val ks = (Frame.getFrowRefVar frame)
				  						val l = List.fold (ks, [], fn (k, l) =>
				  						if (HashTable.inDomain s k) then
					  						let val quals = (HashTable.lookup s k)
					  							val unsubst = List.map (quals, Qualifier.apply (Predicate.PVar var))
					  							val preds = List.map (unsubst, (Predicate.apply_substs subs))
					  						in preds @ l end
				  						else []
				  						)
				  					in 
				  						if ((List.length l) > 0) then SOME l
				  						else NONE
				  					end
				  				| Fvar _ => NONE
				  				| Frecord ([], (_, Qvar (k, _))) => NONE			  				
				  				| _ => NONE (*(print ("Error: anlyFrowRefVar incorrect parameter frame for pat "
				  								^ (Pat.visitPat pat))
				  						; assertfalse ())*)
				  		) varfrs 
				  	in
				  		Common.flatten preds
				  	end
				fun anlyFrowRefVar' pat subs fr s = 
					case fr of 
				 		  Farrow (SOME ppat, f1, f2) => 
				 			let val assertvarfrs' = assertSet ppat f1
				 				val var = Constraintgen.pat_var pat
				 			in
				 				case f2 of 
				 					  Farrow _ => 
				 					  	let val (asserts, assumes) = anlyFrowRefVar' pat subs f2 s
				 					  	in (assertvarfrs' @ asserts, assumes) end
				 					| Fconstr (_, _, (_, Qvar (k, _))) => 
				 						let val quals = HashTable.lookup s k
				 							val unsubst = List.map (quals, Qualifier.apply (Predicate.PVar var))
				 							val preds = List.map (unsubst, (Predicate.apply_substs subs))
				 						in (assertvarfrs', preds) end
				 					| Fconstr (_, _, (_, Qconst quals)) =>
				 						let val unsubst = List.map (quals, (Qualifier.apply (Predicate.PVar var)))
				 							val preds = List.map (unsubst, (Predicate.apply_substs subs))
				 						in (assertvarfrs', preds) end
				 					| Fvar _ => (assertvarfrs', [])
				 					| Frecord ([], _) => (assertvarfrs', []) (* unit type *)
				 					| _ => (print ("Error: maybe returning record fun?" ^ 
										" The current tool implementation is not quite supportive for function returning record"
										^ (Frame.pprint f2) ^ "\n"); 
										assertfalse ()) 
							end  	
						| _ => (print ("Error: In anlyFrowRefVar ill function frame"); assertfalse ())
			in
				anlyFrowRefVar' pat subs fr s
			end
			
			
		(*
		 * Simply analyze the function frame to get to know how each input is attached to a refinement.
		 * Record this kind of information in paramMap
		 * This is used for linking the precondition to a refinment of function input in a solution map
		 * freevars is a set of free variables with their frames
		 *)				
		fun analyzeFunFrame fr paramMap freevars envpending flag = 
			let fun analyzeFunFrame'' pat fr = 
					let val varfrs = Frame.bind pat fr
					in List.foreach (varfrs, fn (var, frame) =>
				  			case frame of 
				  				  Fconstr (tyc, fs, (subs, Qvar (k, _))) => 
				  					if (Tycon.equals (Tycon.list, tyc) andalso List.length fs = 1) then
				  						case (List.first fs) of 
				  							Fconstr (_, _, (_, Qvar (k, _))) => HashTable.insert paramMap ((Predicate.Field ("ele", Predicate.PVar var)), k) 
				  							| Fvar (_, (_, Qvar (k, _)))=> HashTable.insert paramMap ((Predicate.Field ("ele", Predicate.PVar var)), k)
				  							| Frecord (_, (_, Qvar (k, _))) => HashTable.insert paramMap ((Predicate.Field ("ele", Predicate.PVar var)), k) 
				  							| _ => ()
				  					else HashTable.insert paramMap (Predicate.PVar var, k)
				  				| Fconstr (_, _, (_, Qconst qs)) => (
				  					let val p = List.peekMap (qs, fn (v1,v2,p) => case p of
				  							Predicate.Atom (Predicate.PVar x,Predicate.Eq,Predicate.PVar y) => 
				  								if (Var.logic_equals (v2, x)) then SOME y
				  								else NONE  
				  							| _ => NONE
				  						)
				  					in case p of
				  						SOME y => 
				  							let val _ = print "\nrecursively attaching predicate\n"
				  								val f' = HashTable.lookup envpending y
				  							in ignore(analyzeFunFrame'' (Pat.var (var, Type.var(Tyvar.newNoname {equality = false}))) f') end
				  						| NONE => (print "\nCannot attach predicate to this non k refinement\n")
				  					end
				  					)
				  				| Farrow _ => 
			  						let val returnframe = Frame.getFrowFr frame
			  							val paramvars = (*Frame.hofunFramevars frame (var)*) Frame.hofunFramevars_in_version_2 var frame
			  						in
			  							case returnframe of 
			  								Frame.Fconstr (_, _, (_, Qvar (k, _))) => 
			  									HashTable.insert paramMap (Predicate.FunApp ("P" ^ (Int.toString (List.length paramvars)), (Predicate.PVar var) :: paramvars), k)
			  								| Frame.Fvar (_, (_, Qvar (k, _))) => 
			  									HashTable.insert paramMap (Predicate.FunApp ("P" ^ (Int.toString (List.length paramvars)), (Predicate.PVar var) :: paramvars), k)
			  								| Frecord ([], (_, Qvar (k, _))) => ()
			  								| Frame.Frecord (fs, _) =>
			  									List.foreach (fs, fn (f, n) =>
			  										case f of 
			  											Frame.Fconstr (_, _, (subs, Qvar (k, _))) => 
			  												HashTable.insert paramMap (Predicate.Field (n, Predicate.FunApp ("P" ^ (Int.toString (List.length paramvars)), 
			  													(Predicate.PVar var) :: paramvars)), k)
			  											| _ => (print ("\nNested construct " ^ (Frame.pprint returnframe) ^ "\n"); assertfalse ())
			  									)
			  								| _ => (print ("\nUnknow construct " ^ (Frame.pprint frame) ^ "\n"); assertfalse ())
			  						end 
				  				| Frecord ([], (_, Qvar (k, _))) => (* means unit type *)
				  					HashTable.insert paramMap (Predicate.PVar var, k)
				  				| Fvar (a, (_, Qvar (k, _))) => 
				  					HashTable.insert paramMap (Predicate.PVar var, k)
				  				| Frecord (fs, (subs, Qvar (kre, _))) => (
			  						(*List.foreach (fs, fn (f, name) => 
			  							case f of 
			  								Frame.Fconstr (_, _, (_, Qvar (k, _))) => 
			  									HashTable.insert paramMap (Predicate.Field (name, Predicate.PVar var), k)
			  								| Frame.Fvar (_, (_, Qvar (k, _))) =>
			  									HashTable.insert paramMap (Predicate.Field (name, Predicate.PVar var), k)
			  								| Frame.Fsum (_, _, (_, Qvar (k, _))) =>
			  									HashTable.insert paramMap (Predicate.Field (name, Predicate.PVar var), k)
			  								| _ => (print ("\nNested record " ^ (Frame.pprint frame) ^ "\n"); assertfalse ())
			  						);*)
			  						HashTable.insert paramMap (Predicate.PVar var, kre)
			  					)
				  				| Fsum (_, fs, (_, Qvar (k, _))) => (
			  						HashTable.insert paramMap
			  						(Predicate.PVar var, k);
			  						List.foreach (fs, fn (c, f) =>
			  							case f of 
			  								Frame.Fconstr (_, fs', (_, Qvar (k, _))) => (
			  									List.foreachi (fs', fn (i, f') =>
			  										case f' of
			  											Fconstr (_, _, (subs, Qvar (k, _))) => 
			  												HashTable.insert paramMap 
			  												(Predicate.Proj (i+1, Predicate.Field (Con.toString c, Predicate.PVar var)), k)
			  											| Frame.Fvar (_, (_, Qvar (k, _))) =>
			  												HashTable.insert paramMap 
			  												(Predicate.Proj (i+1, Predicate.Field (Con.toString c, Predicate.PVar var)), k)
			  											| Frame.Fsum (_, _, (_, Qvar (k, _))) =>
			  												HashTable.insert paramMap 
			  												(Predicate.Proj (i+1, Predicate.Field (Con.toString c, Predicate.PVar var)), k)
			  											| _ => (print ("\nNested record " ^ (Frame.pprint frame) ^ "\n"); assertfalse ())
			  									)
			  								)
			  								| _ => (print ("\nIllegal type " ^ (Frame.pprint frame) ^ "\n"); assertfalse ())
			  						)
			  					)
				  				| _ => (print ("\nFunction ill typed " ^ (Frame.pprint frame) ^ "\n"); assertfalse ())
				  		);
				  		List.map (varfrs, fn (var, _) => var)
				  	end
				fun analyzeFunFrame' fr paramMap = 
					case fr of 
				 		  Farrow (SOME ppat, f1, f2) => 
				 			let val plist = analyzeFunFrame'' ppat f1
				 			in
				 				case f2 of 
				 					  Farrow _ => 
				 					  	plist @ (analyzeFunFrame' f2 paramMap)
				 					| _ => plist
							end  	
						| Farrow (_, f1, f2) => [] (* the function of the fram returns a function *)
						| _ => (print ("Error: In analyzeFunFrame ill function frame" ^ (Frame.pprint fr)); 
						assertfalse ())
			in
				if flag then analyzeFunFrame' fr paramMap
				else (
					List.foreach (freevars, fn (v, f) => 
						ignore(analyzeFunFrame'' (Pat.var (v, Type.var(Tyvar.newNoname {equality = false}))) f)
					); []
				)
			end
		
		(*
		 * genSubs generates the substitution for function calls. Actuals with Formals 
		 * @param e should be the function application
		 * @param flag let this funcion switch from returning the subs if true or returning the reverse of the subs if false 
		 * @return the subs or [] if e is not given as a function application
		 *)
		fun genApplicationSubs e flag fr =
			let val subs = []
				fun genSubs e subs fr index = 
					case (Exp.node e) of 
						Exp.App (e1, e2) => 
							(let val ((subs, fr), index) = genSubs e1 subs fr index
							in
								(case fr of 
								Frame.Farrow (l, f, f') => 
								(case l of 
								SOME pat => 
								(case (Exp.node e2) of
					        		Exp.Record r =>
					        			(
					        			let 
					        				val pexprlist = Vector.toListMap ((Record.toVector(r)), (Constraintgen.expression_to_pexpr o (fn (a, b) => b)))  
					        			in
					        				((List.foldr ((Pattern.bind_pexpr pat (Predicate.Tuplelist pexprlist)), subs, fn (sub, subs) => sub :: subs), f'), index+1)
					        			end			        			
					        			) 		        		
				        			| _ => ((List.foldr ((Pattern.bind_pexpr pat (Constraintgen.expression_to_pexpr e2)), subs, fn (sub, subs) => sub :: subs), f'), index+1)
			        			)
			        			| NONE =>
			        			(case (Exp.node e2) of
					        		Exp.Record r =>
					        			(
					        			let val pexprlist = Vector.toListMap ((Record.toVector(r)), (Constraintgen.expression_to_pexpr o (fn (a, b) => b)))  
					        				val pat = Pat.var (Var.fromString ("local_arg" ^ (Int.toString index)), Type.var(Tyvar.newNoname {equality = false}))
					        			in
					        				((List.foldr ((Pattern.bind_pexpr pat (Predicate.Tuplelist pexprlist)), subs, fn (sub, subs) => sub :: subs), f'), index+1)
					        			end			        			
					        			) 		        		
				        			| _ => 
				        				let val pat = Pat.var (Var.fromString ("local_arg" ^ (Int.toString index)), Type.var(Tyvar.newNoname {equality = false}))
				        				in
				        					((List.foldr ((Pattern.bind_pexpr pat (Constraintgen.expression_to_pexpr e2)), subs, fn (sub, subs) => sub :: subs), f'), index+1)
			        					end
			        			)	 
			        			)
			        			| _ => assertfalse ())	
			        		end
			        		)
						| _ => ((subs, fr), index)
				val ((subs, _), _) = genSubs e subs fr 0
				val subs = List.map (subs, fn (v, p) => (v, (Predicate.simplify_predpexpr p)))
			in
				if flag then subs
				else
					Common.map_partial (fn (v, p) => 
						case p of 
							Predicate.PVar pvar => SOME (pvar, Predicate.PVar v)
							| _ => NONE
					) subs
				
					(*List.map (subs, fn (v, p) => 
						case p of 
							Predicate.PVar pvar => (pvar, Predicate.PVar v)
							Predicate.PInt i => (i, )
							| _ => (print ("Our tool currently need SSA for function input strictly."); assertfalse ()))
					*)
			end
		
		fun genApplicationSubsByType e ty index =
			let val subs = []
				fun genSubs e subs ty index = 
					case (Exp.node e) of 
						Exp.App (e1, e2) => 
							(let val ((subs, ty), index) = genSubs e1 subs ty index
							in
								(case ty of 
								Type_desc.Tarrow (t, t') => 
				        			(case (Exp.node e2) of
						        		Exp.Record r =>
						        			(
						        			let val pexprlist = Vector.toListMap ((Record.toVector(r)), (Constraintgen.expression_to_pexpr o (fn (a, b) => b)))  
						        				val pat = Pat.var (Var.fromString ("local_arg" ^ (Int.toString index)), Type.var(Tyvar.newNoname {equality = false}))
						        			in
						        				((List.foldr ((Pattern.bind_pexpr pat (Predicate.Tuplelist pexprlist)), subs, fn (sub, subs) => sub :: subs), t'), index+1)
						        			end			        			
						        			) 		        		
					        			| _ => 
					        				let val pat = Pat.var (Var.fromString ("local_arg" ^ (Int.toString index)), Type.var(Tyvar.newNoname {equality = false}))
					        				in
					        					((List.foldr ((Pattern.bind_pexpr pat (Constraintgen.expression_to_pexpr e2)), subs, fn (sub, subs) => sub :: subs), t'), index+1)
				        					end
				        			)	 
			        			| _ => assertfalse ())	
			        		end
			        		)
						| _ => ((subs, ty), index)
				val ((subs, _), _) = genSubs e subs ty index
				val subs = List.map (subs, fn (v, p) => (v, (Predicate.simplify_predpexpr p)))
			in subs end
			
		(*
		 * genMatchcaseSubs generates the substitution for match-case pattern matchings.
		 * @param test should be the match-case test, i.e. test sould be record
		 * @param pat should be the case-pattern
		 * @return the subs or [] if test is not given as a match-case
		fun genDeepSubs test pat =
			let val subs = []
				fun genSubs test pat subs = 
					if (Type.isBool (Exp.ty test)) then subs
					else
						let val pexprs = Constraintgen.matchcase_exp_to_pexpr test
						in
							if Pattern.is_deep pat then (print "In Deep Gen Subs";
								case (Pat.node pat) of 
									(Pat.Tuple pats) => List.fold2 ((Vector.toList pats), pexprs, subs, (fn (pat, pexpr, subs) => 
															List.foldr ((Pattern.bind_pexpr pat pexpr), subs, fn (sub, subs) => sub :: subs)
															))
									| _ => (print "Error: not deep subs"; assertfalse ()))
							else subs
						end 
				val subs = genSubs test pat subs
			in
				List.map (subs, fn (v, p) => 
					case p of 
						Predicate.PVar pvar => (pvar, Predicate.PVar v)
						| _ => (print ("Our tool currently need SSA for function input strictly."); assertfalse ()))
			end
		 *)	
		val visitingFlag = ref true
		
		fun getFunctionBody e = TestRun.getFunctionBody e
		
		(*fun getRecursiveFunTerminationCondition e = case e of 
			Exp.Case {rules, ...} => 
				let val realfunbody = #exp (Vector.last rules)
				in
			| _ => (print "\nfunction body problem\n"; assertfalsle()) *)
		
		fun getFunctionParams e matching_subs = 
			let 
				(*val e = getFunctionBody e*)
				fun mf bpat test index = case (Pat.node bpat, Exp.node test) of 
	     	    	((Pat.Tuple pats), (Exp.Record r)) => 
	     			 	Vector.foreach2 (pats, Record.range r, fn (pat, exp) => mf pat exp NONE)
	     			| (Pat.Var pat, Exp.Var (varf, _)) => 
	     				(case index of 
	     					SOME index => List.push (matching_subs, (pat, Predicate.Field (index, Predicate.PVar (varf()))))
	     					| NONE => List.push (matching_subs, (pat, Predicate.PVar (varf ()))))
	     			| (Pat.Tuple pats, Exp.Var (varf, _)) => 
	     				if (Vector.length pats = 1) then mf (List.first (Vector.toList pats)) test NONE
	     				else (
	     					Vector.foreachi (pats, fn (i, p) => mf p test (SOME (Int.toString (i+1))))
	     				)
	     			| (Pat.Record pats, Exp.Var (varf, _)) =>
	     				Vector.foreach (Record.toVector pats, fn (f, p) => mf p test (SOME (Field.toString f)))
	     			| _ => (print ("Error in pat and test matching" ^ (CoreML.Pat.visitPat bpat) ^ (CoreML.visitExp test)); assertfalse ())
			in
				case (Exp.node e) of
					Exp.Case {rules, test, ...} =>
						Vector.foreach (rules, fn ({exp, pat, lay}) => mf pat test NONE)
					| _ => (print "\ngetFunctionParams matching error\n"; assertfalse ())
			end
		
		
		(*
		 * visitExpForward collect the experssion along the path
		 * @pat is what will be assigned to
		 * @forwardexp is an important flag which should be assert function (assert), function application (precondition), function definitaion (postcondition)
		 * @param exp the modular binding expression 
		 * @param path the path locations (for if-then-else only now)
		 * @param explist from which the result of Exp.list can be found
		 * @param isSeekingPost
		 *)
		fun visitExpForward tpat forwardexp ee path explist isSeekingPost = (
			(*print ("\n************for pat " ^ (CoreML.Pat.visitPat tpat) ^ " ee: " ^ (CoreML.visitExp ee) ^ " endexp ****\n");*)
			if (!visitingFlag) then 
				case (Exp.node ee, path) of    
					(*(Exp.Case {rules, test, ...}, []) =>
						let fun mf bpat test = case (Pat.node bpat, Exp.node test) of 
		         	    	  ((Pat.Tuple pats), (Exp.Record r)) => 
		         			 	Vector.foreach2 (pats, Record.range r, fn (pat, exp) => List.push (explist, (pat, exp, Selection)))
		         			| (Pat.Var pat, Exp.Var (varf, _)) => List.push (explist, (bpat, test, Selection))
		         			| (Pat.Tuple pats, Exp.Var (varf, _)) => 
		         				List.push (explist, (List.first (Vector.toList pats), test, Selection))
		         			| _ => (print "Error in pat and test matching"; assertfalse ())
		         		in
			         		Vector.fold (rules, path, fn ({exp, pat, lay}, path) => 
			         			(mf pat test; visitExpForward tpat forwardexp exp path explist isSeekingPost)
			         		)
		         		end	
		        	|*) (Exp.Case {rules, test, ...}, (path as switch::path')) =>
		        	if (Type.isBool (Exp.ty test)) then (
		        		(*print "\n***Enter a branch***\n";*)
		        		if (isSeekingPost andalso (List.length path' = 0)) (* beyond the divergingpoint thus can stop here *)
		        		then (visitingFlag := false; []) 
		        		else (
		        			(*print "\nEntered._________\n"; print ("switch: " ^ (Int.toString switch) ^ "\n");*)
		        			Vector.fold (rules, path, (fn ({exp, pat, lay}, path) => 
		         				(case (Pat.node pat) of 
					  			Pat.Con {arg=arg',con=con',targs=targs'} => (
					  				(case Con.toString (con') of
						  		  		  "true" => if (switch = 1) then
						  		  		  				(List.push (explist, (dummypat, test, ConditionalTrue)); 
						  		  		  				visitExpForward tpat forwardexp exp path' explist isSeekingPost)
						  		  		  			else path
						  				| "false" => if (switch = 0) then
						  		  		  				(List.push (explist, (dummypat, test, ConditionalFalse)); 
						  		  		  				visitExpForward tpat forwardexp exp path' explist isSeekingPost)
						  		  		  			else path
						  				| _ => (print "visiteExpForward if-then-else error"; assertfalse ()))) (* End of case2 *)
						  		| _ => (print ("visiteExpForward if-then-else error"); assertfalse ())) (* End of case1 *)
		         			) (* End of fn *)
		         			)))
		        	else
		        		let fun mf bpat test = case (Pat.node bpat, Exp.node test) of 
		         	    	  ((Pat.Tuple pats), (Exp.Record r)) => 
		         			 	Vector.foreach2 (pats, Record.range r, fn (pat, exp) => List.push (explist, (pat, exp, Selection)))
		         			| (Pat.Var pat, Exp.Var (varf, _)) => List.push (explist, (bpat, test, Selection))
		         			| (Pat.Tuple pats, Exp.Var (varf, _)) => List.push (explist, (List.first (Vector.toList pats), test, Selection))
		         			| (Pat.Con con, Exp.Var (varf, _)) => List.push (explist, (bpat, test, Selection)) 
		         			| _ => (print "Error in pat and test matching"; assertfalse ())
		         			val {exp, pat, lay} = List.nth (Vector.toList rules, switch)
		         		in
			         		mf pat test;
			         		visitExpForward tpat forwardexp exp path' explist isSeekingPost
		         		end	
		         		
			       | (Exp.Let (ds, e), path) => 
			       		let val path = Vector.fold (ds, path, fn (d, path) => visitDecForward d forwardexp path explist isSeekingPost)
			       		in visitExpForward tpat forwardexp e path explist isSeekingPost end
			       | (Exp.Seq es, path) => 
			       		let val es = Vector.toList es
			       			val e' = List.last es
			       			val es' = List.allButLast es
			       			val path = List.fold (es', path, fn (e'', path) => visitExpForward dummypat forwardexp e'' path explist isSeekingPost)
			       		in 
			       			visitExpForward tpat forwardexp e' path explist isSeekingPost
			       		end
			       | (Exp.App (e1, e2), path) => (case (Exp.node e1) of 
		      			(Exp.Con (c, targs)) => (List.push (explist, ( tpat, ee, Assignment)); path)
		      			| _ => 
				         	let val funname = Constraintgen.getFunctionAppName ee
				         		(*val _ = print ("\nDealing with app of " ^ (funname) ^ "\n")*)
				         	in
			       				case (Exp.node forwardexp) of 
			       					Exp.App _ =>
		       							if (String.hasPrefix (CoreML.visitExp ee, {prefix = CoreML.visitExp forwardexp})) 
		       							then (visitingFlag := false; []) (* the precondtion, stop collecting more statements *)
		       							else (List.push (explist, ( tpat, ee, Assignment)); path) (* ordinary fun call, add to list *)
			       					| _ => (List.push (explist, ( tpat, ee, Assignment)); path) (* the post condition, just put it into list *)
				       		end
				       	)
			       | (e, path) => (List.push (explist, ( tpat, ee, Assignment)); path)
			       (*| _ => assertfalse ()*)
			else [])
		
		and visitDecForward d forwardexp path explist isSeekingPost =
			case d of
	       		  Dec.Datatype v => path
	       		| Dec.Exception ca => path
	       		| Dec.Fun {decs, tyvars, ...} => path
	       		| Dec.Val {rvbs, tyvars, vbs, ...} => Vector.fold (vbs, path, fn ({exp, pat, ...}, path) => visitExpForward pat forwardexp exp path explist isSeekingPost) 
				
		fun logicopToPred exp fenv = 
			case (Exp.node exp) of
				Exp.App (e1, e2) => (
					case (Exp.node e1,Exp.node e2) of
						(Exp.Var opr, Exp.Record r) =>
							let val (funname, funpat) = Constraintgen.getFunctioinAppPat exp
								val funvar = Constraintgen.pat_var funpat
							in
								if (String.equals (funname, "&&") orelse String.equals (funname, "||")) then
									let val lr = Vector.toListMap ((Record.toVector r), (fn (a, b) => b))
										val l = List.first lr
										val r = List.last lr
										val pl = logicopToPred l fenv
										val pr = logicopToPred r fenv
									in
										if (String.equals (funname, "&&")) then
											(Predicate.And (pl, pr))
										else if (String.equals (funname, "||")) then
											(Predicate.Or (pl, pr))
										else (print "\n...well...unreachable\n"; assertfalse ())
									end
								else if (Lightenv.mem funvar fenv) then 
					  				let val fr = Lightenv.find funvar fenv
					  					val fr' = getFrowFr fr
					  					val (conditionalE, fr) = case fr' of
					  					Frame.Fconstr (a, b, (subs,Frame.Qconst[(v1,v2,Predicate.Iff (v3,p))])) =>
											if Predicate.logic_equals_pexp v3 (Builtin.tag (Predicate.PVar v2)) then (p, fr)
									        else (print ("Cannot perfrom predicate transforme due to unknown if condition " ^ (Pat.visitPat funpat)); 
												assertfalse ())
										| _ => (print ("Error: cannot perfrom predicate transforme due to unknown if condition " ^ (Pat.visitPat funpat)); 
												assertfalse ())	
										val subs = genApplicationSubs exp true fr
									in
										Predicate.apply_substs subs conditionalE  
									end
								else (print "\nlogic operator cannot be transformed to predicate\n"; assertfalse ())
							end
						| _ => (print "\nError logic oerator given\n"; assertfalse ())
				)
				| _ => (print "\nError logic oerator given\n"; assertfalse ())
		
		
		(*
		 * pred_transformer is based on Predicate transformer semantics which can be generaly found from:
		 * http://en.wikipedia.org/wiki/Predicate_transformer_semantics
		 * @param pred the predicate
		 * @param exp the expression
		 * @param bindingframe according to it we found the frame thus the summary of the function application
		 * @fenv from fenv we can find the summary type for the built-ins such as {+,-*,/} and {>,>=,=,<=,<}
		 * @param s the solution hash table
		 * @return the transformed predicate
		 *)
		fun pred_transform pred exp bindingframe fenv s fr = 
			case exp of 
				  (pat, ee, Assignment) => (
					case (Exp.node ee) of
						Exp.App (e1, e2) => (
							case (Exp.node e1, Pat.node pat) of
							(Exp.Con (c, targs), Pat.Var pv) => (* pat = Constructor i.e. x = con (z, y) *) (
								case (Exp.node e2) of
									Exp.Var (var, _) => 
										let val px = Predicate.Proj (1, Predicate.Field (Con.toString c, Predicate.PVar pv))  
										in Predicate.subst2 (Predicate.PVar (var())) px pred end
									| Exp.Const f => (case (Type.toMyType (Exp.ty ee)) of
			  							Type_desc.Tconstr (t, []) => 
				  	  		  				if (Tycon.isIntX t) then
				  	  		  					let val px = Predicate.Proj (1, Predicate.Field (Con.toString c, Predicate.PVar pv))  
				  	  		  						val constval = f() in case constval of 
				  	  		  			     		Const.IntInf n => Predicate.subst2 (Predicate.PInt (IntInf.toInt n)) px pred 
									       			| Const.Word n => Predicate.subst2 (Predicate.PInt (WordX.toInt n)) px pred
									       			| _ => (print "toPredIntError\n"; assertfalse ())
				  	  		  					end  		
				  	  		  				else pred
			  	  						| _ => pred
				  	  				)
									| Exp.Record r => 
										let val rs = Vector.toList (Record.range r)
										in
											List.foldi (rs, pred, fn (index, re, pred) =>
												case (Exp.node re) of
													Exp.Var (var, _) => 
														let val px = Predicate.Proj (index+1, Predicate.Field (Con.toString c, Predicate.PVar pv))
														in Predicate.subst2 (Predicate.PVar (var())) px pred end 
													| _ => (print ("\nNested record of constructor " ^ (CoreML.visitExp ee) ^ "\n"); assertfalse ())
											)
										end
									| _ => (print ("\nConstructor ill formed " ^ (CoreML.visitExp ee) ^ "\n"); assertfalse ()) 
							)	
							| _ => (* For function type, we would like to use the assume and assert semantics; builtin functions needs to
						  						be dealt with specially *)
							let 
								val (funname, funpat) = Constraintgen.getFunctioinAppPat ee
								val _ = print ("\n______ pred_transform funtion " ^ funname ^ "_______\n")
								val funvar = Constraintgen.pat_var funpat
								val arithops = ["+", "-", "*", "/", "array_0", "length_0", "nRows_0", "nCols_0", "div", "mod"]
								val logicops = ["not", "!_0", ":=_0", "sin", "cos", "real", "ignore_0", "make_str"]
								val ((asserts, assumes), flag) = 
									if HashTable.inDomain bindingframe funpat then
										let val fr = HashTable.lookup bindingframe funpat
											val subs = genApplicationSubs ee true fr
										in (anlyFrowRefVar pat subs fr s, 0) end
									else if ((Lightenv.mem funvar fenv) andalso 
												not (List.exists (arithops, fn arithop => (String.compare (arithop, funname) = EQUAL)))) then
										let val fr = Lightenv.find funvar fenv
											val subs = genApplicationSubs ee true fr
										in (anlyFrowRefVar pat subs fr s, 0) end
									else if ((Lightenv.mem funvar fenv) andalso 
												(List.exists (arithops, fn arithop => (String.compare (arithop, funname) = EQUAL)))) then
										let val fr = Lightenv.find funvar fenv
											val subs = genApplicationSubs ee true fr
											(*val _ = print "\nsubs is "
											val _ = List.foreach (subs, fn (v, p) => print ("\nv is " ^ (Var.toString v) ^ "  p is " ^ (Predicate.pprint_pexpr p)))
											val _ = print "\n"*)
										in (anlyFrowRefVar pat subs fr s, 1) end
									else if (List.exists (logicops, fn logicop => (String.compare (logicop, funname) = EQUAL))) then
										(([], []), 1)
									else (* If the function does not exist in both binding_frame or lightenv, we believe it is 
									      * higher order function (function parameter) *)
										(([], []), 2)
										(*(print ("Cannot perfrom predicate transforme due to unknown function call " ^ (Pat.visitPat funpat)); 
										assertfalse ())*)	
							in
								if (flag = 1) then	(
									(*print "\nflag is 1 so deal with length_0,+,-,...\n";*)
									List.fold (assumes, pred, fn (assume, pred) => 
										case assume of 
											  (Predicate.Atom (e', Predicate.Eq, exp)) => 
											  	if (List.exists (["+","-","*","/","div","mod"], fn arithop => (String.compare (arithop, funname) = EQUAL))) then (
											  	(*print ("\nassumption is " ^ Predicate.pprint (assume) ^ "\n");*)
												Predicate.subst exp (Constraintgen.pat_var pat) pred 
												)
												else if (String.equals (funname, "array_0")) then (
													print ("\nassumption is " ^ Predicate.pprint (assume) ^ "\n");
													print ((Predicate.pprint_pexpr e') ^ "\n");
													print ((Predicate.pprint_pexpr exp) ^ "\n");
													Predicate.subst2 e' exp pred
												)
												else if (String.equals (funname, "nRows_0")) then (
													print ("\nassumption is " ^ Predicate.pprint (assume) ^ "\n");
													print ((Predicate.pprint_pexpr e') ^ "\n");
													print ((Predicate.pprint_pexpr exp) ^ "\n");
													Predicate.subst2 exp e' pred
												)
												else if (String.equals (funname, "nCols_0")) then (
													print ("\nassumption is " ^ Predicate.pprint (assume) ^ "\n");
													print ((Predicate.pprint_pexpr e') ^ "\n");
													print ((Predicate.pprint_pexpr exp) ^ "\n");
													Predicate.subst2 exp e' pred
												)
												else ( (*current for length_0 only*)
													print ("\nassumption is " ^ Predicate.pprint (assume) ^ "\n");
													print ((Predicate.pprint_pexpr e') ^ "\n");
													print ((Predicate.pprint_pexpr exp) ^ "\n");
													Predicate.subst2 exp e' pred
												)
											| (Predicate.Iff (e', pd)) => (* current for function not only *)
												(print ("\nassumption is " ^ (Predicate.pprint assume) ^ "\n"); assertfalse ())
												(*Predicate.subst (Predicate.Not e2) x pred*)
											| _ => (print ("assumption will not be used " ^ (CoreML.visitExp ee) ^ ": " ^ (Predicate.pprint assume)); pred)
									)
								)
								else if (flag = 0) then (* This is a real function, we need to know the precondition of this function *)
									(*let val assumes = Common.map_partial (fn assume => 
										if List.exists ((Predicate.andPredicateList pred), fn p => Predicate.logic_equals (p, assume)) then
											SOME assume
										else NONE) assumes
										val pred = 
											if ((List.length assumes) > 0) then
												List.fold (assumes, pred, fn (assume, pred) => Predicate.imply assume pred)
											else pred
									in
										List.fold (asserts, pred, fn (assert, pred) => Predicate.ando assert pred)
									end*)
									pred	
								else (* We believe this is the case of higher order funcall
								 	  * However, when replacing, need to consider the version of it. 
								 	  *) 
								 	let val version = (*Var.getVersion funvar*) 1
								 		fun paramIndex e = 
							      			case (Exp.node e) of
							      				Exp.Var _ => ((~1), [])
							      				| Exp.App (e1, e2) => 
							      					let val (index, pvs) = paramIndex e1  
							      					in (1+index, pvs @ [Predicate.FunApp (("arg" ^ (Int.toString (1+index))), [Predicate.PVar funvar])]) end							      					
							      				| _ => (print "\nError function form\n"; assertfalse ())
			      						val (_, pvs) = paramIndex ee
								 		val mp = Predicate.FunApp (("P" ^ (Int.toString (List.length pvs))), (Predicate.PVar funvar) :: pvs)  (*version*)
									in Predicate.subst mp (Constraintgen.pat_var pat) pred end
						  	end
						)
						(* ordinary assignment can be dealt by: wp(x:=E, R) = R[x<-E] *)
						| Exp.Var (var, targs) => Predicate.subst (Predicate.PVar (var())) (Constraintgen.pat_var pat) pred
						| Exp.Const f =>
							(case (Type.toMyType (Exp.ty ee)) of
				  				Type_desc.Tconstr (t, []) => 
					  	  		  	if (Tycon.isIntX t) then
					  	  		  		let val constval = f() in
					  	  		  			case constval of 
					  	  		  			     Const.IntInf n => Predicate.subst (Predicate.PInt (IntInf.toInt n)) (Constraintgen.pat_var pat) pred 
										       | Const.Word n => Predicate.subst (Predicate.PInt (WordX.toInt n)) (Constraintgen.pat_var pat) pred
										       | _ => (print "toPredIntError\n"; assertfalse ())
					  	  		  		end  		
					  	  		  	else pred
				  	  			| _ => pred
				  	  		)
				  	  	| Exp.Record r => 
				  	  		let val plist = (Record.toVector r)
				  	  			val _ = print ("\nComes here " ^ (Vector.fold (plist, "", fn ((pf, pv), str) => 
				  	  			(str ^ "; Field is " ^ (Field.toString pf) ^ " RExp is " ^ (CoreML.visitExp pv)))) ^ "\n")
				  	  			val _ = print ("\npat is " ^ (CoreML.Pat.visitPat pat))
				  	  		in
				  	  			case (Pat.node pat) of 
				  	  				Pat.Var v =>
				  	  					Vector.foldi (plist, pred, fn (i, (pf, pv), pred) =>
				  	  						case (Exp.node pv) of 
				  	  							Exp.Var (pv, _) => 
				  	  								let val pd = Predicate.subst2 (Predicate.PVar (pv())) 
				  	  									(Predicate.Field (Field.toString pf, Predicate.PVar (Constraintgen.pat_var pat))) pred
				  	  								in
				  	  									Predicate.subst2 (Predicate.PVar (pv())) 
				  	  									(Predicate.Field (Int.toString (i+1), Predicate.PVar (Constraintgen.pat_var pat))) pd
				  	  								end
				  	  							| Exp.Const f => (
													case (Type.toMyType (Exp.ty pv)) of
										  	  		  Type_desc.Tconstr (t, []) => 
										  	  		  	if (Tycon.isIntX t) then
										  	  		  		let val constval = f()
										  	  		  			val p' = case constval of 
										  	  		  			     Const.IntInf n => (Predicate.PInt (IntInf.toInt n))
															       | Const.Word n => (Predicate.PInt (WordX.toInt n))
															       | _ => (print "toPredIntError\n"; assertfalse ())
															in 
																Predicate.subst2 p' 
				  	  											(Predicate.Field (Field.toString pf, Predicate.PVar (Constraintgen.pat_var pat))) pred
										  	  		  		end  		
										  	  		  	else pred
										  	  		| _ => pred
										  	  	)
				  	  							| _ => (print "\nNexted recored/tuple is not supported\n"; assertfalse ())
				  	  					)
				  	  				| Pat.Record tr => 
				  	  					Vector.fold2 (Record.range tr, plist, pred, fn (pat, (pf, pv), pred) =>
				  	  						case (Exp.node pv) of 
				  	  							Exp.Var (pv,_) => Predicate.subst (Predicate.PVar (pv())) (Constraintgen.pat_var pat) pred 
				  	  							| _ => (print "\nNested record is not supported\n"; assertfalse ())
				  	  					)
				  	  				| Pat.Tuple ts => 
				  	  					Vector.fold2 (ts, plist, pred, fn (pat, (pf, pv), pred) =>
				  	  						case (Exp.node pv) of 
				  	  							Exp.Var (pv,_) => Predicate.subst (Predicate.PVar (pv())) (Constraintgen.pat_var pat) pred
				  	  							| _ => (print "\nNested tuple is not supported\n"; assertfalse ())
				  	  					)
				  	  				| _ => (print "\nPat cannot be dealed\n"; assertfalse ())
				  	  		end
						| _ => (print ("Error: SML program not in SSA1, the error expression is " ^ (visitExp ee)); 
							case (Exp.node ee) of
								Exp.Case _ => (* skip unrelated if-then-else *) pred
								| _ => assertfalse ())
				  )	
				| (pat, ee, ConditionalTrue) => (* ConditionalTrue wp(if E then S1..., R) = (E => wp(S1, R)) *)
					(case (Exp.node ee) of 
						  Exp.App (e1, e2) => (* must find these funs in fenv becuase they should be {>,>=,=,<=,<} *)
						  	let (*val (funname, funpat) = Constraintgen.getFunctioinAppPat ee
								val funvar = Constraintgen.pat_var funpat
						  		val (conditionalE, fr) = 
						  			if (Lightenv.mem funvar fenv) then 
						  				let val fr = Lightenv.find funvar fenv
						  					val fr' = getFrowFr fr
						  				in case fr' of
						  					Frame.Fconstr (a, b, (subs,Frame.Qconst[(v1,v2,Predicate.Iff (v3,p))])) =>
												if Predicate.logic_equals_pexp v3 (Builtin.tag (Predicate.PVar v2)) then (p, fr)
										        else (print ("Cannot perfrom predicate transforme due to unknown if condition " ^ (Pat.visitPat funpat)); 
													assertfalse ())
											| _ => (print ("Error: cannot perfrom predicate transforme due to unknown if condition " ^ (Pat.visitPat funpat)); 
													assertfalse ())	
										end
						  			else (print ("Error: cannot perfrom predicate transforme due to unknown if condition " ^ (Pat.visitPat funpat)); 
										assertfalse ())	
								val subs = genApplicationSubs ee true fr
								val conditionalE = Predicate.apply_substs subs conditionalE
								*)
								val conditionalE = logicopToPred ee fenv
						  	in
						  		if (Predicate.logic_equals (pred, Predicate.True)) then conditionalE
						  		else Predicate.imply conditionalE pred
						  	end
						| Exp.Var (var, targs) =>
							let val conditionE = Predicate.iffo (Predicate.PVar (var())) (Predicate.True)
							in Predicate.imply conditionE pred end
						| _ => (print ("Error: SML program not in SSA2, the error expression is " ^ (visitExp ee)); assertfalse ()))
				| (pat, ee, ConditionalFalse) => (* ConditionalFalse wp(if E then ...else S2, R) = (not E => wp(S2, R)) *)
					(case (Exp.node ee) of
						  Exp.App (e1, e2) => 
						  	let (*val (funname, funpat) = Constraintgen.getFunctioinAppPat ee
						  		val funvar = Constraintgen.pat_var funpat
						  		val (conditionalE, fr) = 
						  			if (Lightenv.mem funvar fenv) then 
						  				let val fr = Lightenv.find funvar fenv
						  					val fr' = getFrowFr fr
						  				in case fr' of
						  					Frame.Fconstr (a, b, (subs,Frame.Qconst[(v1,v2,Predicate.Iff (v3,p))])) =>
												if Predicate.logic_equals_pexp v3 (Builtin.tag (Predicate.PVar v2)) then (Predicate.Not p, fr)
										        else (print ("Cannot perfrom predicate transforme due to unknown if condition " ^ (Pat.visitPat funpat)); 
													assertfalse ())
											| _ => (print ("Error: cannot perfrom predicate transforme due to unknown if condition " ^ (Pat.visitPat funpat)); 
													assertfalse ())
										end
						  			else (print ("Error: Cannot perfrom predicate transforme due to unknown if condition " ^ (Pat.visitPat funpat)); 
										assertfalse ())	
								val subs = genApplicationSubs ee true fr
								val conditionalE = Predicate.apply_substs subs conditionalE*)
								val conditionalE = Predicate.Not (logicopToPred ee fenv)
						  	in
						  		if (Predicate.logic_equals (pred, Predicate.True)) then conditionalE
						  		else Predicate.imply conditionalE pred
						  	end
						| Exp.Var (var, targs) => 
							let val conditionE = Predicate.iffo (Predicate.PVar (var())) (Predicate.Not Predicate.True)
							in Predicate.imply conditionE pred end
						| _ => (print ("Error: SML program not in SSA3, the error expression is " ^ (visitExp ee)); assertfalse ()))
				| (pat, ee, Selection) => (* Selection (only simple version): wp(x:=E, R) = R[x<-E] *)
					(
					print ("\nSelection here pat is " ^ (CoreML.Pat.visitPat pat) ^ "\n"); 
					case (Exp.node ee) of 
						  Exp.Var (var, targs) => (
						  	case (Pat.node pat) of
						  		Pat.Var pvar => Predicate.subst (Predicate.PVar (var())) pvar pred
						  		| Pat.Tuple ts => 
						  			Vector.foldi (ts, pred, fn (i, pt, pred) =>
										case (Pat.node pt) of
											(Pat.Var ptvar) => Predicate.subst (Predicate.Field (Int.toString i, Predicate.PVar (var()))) (ptvar) pred
											| _ => 
											(print ("\nPattern matching error " ^ (CoreML.visitExp ee) ^ "/" ^ (CoreML.Pat.visitPat pat) ^ "\n"); assertfalse ())
									)
						  		| Pat.Record tr =>
						  			Vector.fold ((Record.toVector tr), pred, fn ((pf, pt), pred) =>
										case (Pat.node pt) of
											(Pat.Var ptvar) => Predicate.subst (Predicate.Field (Field.toString pf, Predicate.PVar (var()))) (ptvar) pred
											| _ => 
											(print ("\nPattern matching error " ^ (CoreML.visitExp ee) ^ "/" ^ (CoreML.Pat.visitPat pat) ^ "\n"); assertfalse ())
									)
						  		| Pat.Con {arg=arg, con=con, targs=targs} => (
						  			case (Predicate.last_Not_Or pred) of 
						  				Predicate.Not Predicate.True => ( (* This is the case we want to show an invisible path *)
						  					Predicate.imply 
						  						(Predicate.Atom (
						  							Predicate.FunApp ("__constr", [Predicate.PVar (var())]), 
						  							Predicate.Eq,
						  							Predicate.PInt (Constraintgen.getConIndex con (CoreML.Pat.ty pat))
						  						)) pred
						  				)
						  				| _ => (
						  					(* processing user defined data type *)
								  			case arg of (* processing user defined data type *)
								  				SOME arg => 
													let val predvars = Predicate.vars pred
												 		val conargs = case (Pat.node arg) of 
												 			Pat.Var pvar => [pvar]
												 			| Pat.Tuple t => Vector.toListMap (t, fn tp => 
												 					case (Pat.node tp) of 
												 						Pat.Var tpv => tpv
												 						| _ => (print ("\nNested construct " ^ (CoreML.Pat.visitPat pat) ^ "\n"); assertfalse ())
												 				)
												 			| Pat.Record r => Vector.toListMap (Record.range r, fn rp => 
												 					case (Pat.node rp) of
												 						Pat.Var rpv => rpv
												 						| _ => (print ("\nNested construct " ^ (CoreML.Pat.visitPat pat) ^ "\n"); assertfalse ())
												 				)
												 			| _ => (print ("\nConstructor ill formed " ^ (CoreML.Pat.visitPat pat) ^ "\n"); assertfalse ())
												 	in
												 		if (String.equals (Con.toString con, "::")) then (
												 			let val predvar = List.first conargs
						  									in Predicate.subst (Predicate.Field ("ele", Predicate.PVar (var ()))) predvar pred end
						  								) 
						  								else (
												 		List.fold (predvars, pred, fn (predvar, pred) =>
												 			case (List.index (conargs, fn conarg => (Var.logic_equals (conarg, predvar)))) of
												 				SOME index (* var,con,index *) => 
												 				Predicate.subst (
												 				Predicate.Proj (index+1, Predicate.Field (Con.toString con, Predicate.PVar (var())))) 
												 				predvar pred 
												 				| NONE => pred 
												 		)
												 		)
												 	end
								  				| NONE => pred
						  				)	 
						  			)
						  		| _ => (print ("\nUnsupported pattern " ^ (CoreML.Pat.visitPat pat) ^ "\n"); assertfalse ())
						  )
						| Exp.Record r => ( 
							case ((Pat.node pat)) of 
								Pat.Tuple ts =>
									Vector.fold2 (Record.toVector r, ts, pred, fn ((rf, re), pt, pred) =>
										case (Exp.node re, Pat.node pt) of
											(Exp.Var (var, _), Pat.Var ptvar) => Predicate.subst (Predicate.PVar ptvar) (var()) pred
											| _ => 
											(print ("\nPattern matching error " ^ (CoreML.visitExp ee) ^ "/" ^ (CoreML.Pat.visitPat pat) ^ "\n"); assertfalse ())
									)
								| Pat.Record tr => 
									Vector.fold2 (Record.toVector r, (Record.toVector tr), pred, fn ((rf, re), (_, pt), pred) =>
										case (Exp.node re, Pat.node pt) of
											(Exp.Var (var, _), Pat.Var ptvar) => Predicate.subst (Predicate.PVar ptvar) (var()) pred
											| _ =>
											(print ("\nPattern matching error " ^ (CoreML.visitExp ee) ^ "/" ^ (CoreML.Pat.visitPat pat) ^ "\n"); assertfalse ())
									)
								| _ => (print ("\nPattern matching error " ^ (CoreML.visitExp ee) ^ "/" ^ (CoreML.Pat.visitPat pat) ^ "\n"); assertfalse ())
							)
						| _ => (print ("\nError: Current implementation only support simple match-case which is of vars pattern only\n"); assertfalse ())
					)
		
		
		fun removeUnecessary explist = 
			if (List.length (!explist) > 0) then
				let val (p, e, expclass) = List.pop explist
				in
					case expclass of
						  ConditionalTrue => List.push (explist, (p, e, expclass))
						| ConditionalFalse => List.push (explist, (p, e, expclass))
						| _ => removeUnecessary explist
				end
			else (print "Error: No conditionals in the path; that is impossible theoretically"; assertfalse ())
			
		 	
		exception Not_Converge 
		
		(*fun parseConstrPredicate pexp = 
			case pexp of 
				Predicate.Proj (index, pexp) => (
					case pexp of 
						Predicate.Field (constrName, pexp) => (
							case pexp of 
								Predicate.PVar _ => [constrName, idnex] 
								| _ => [constrName, index] @ parseConstrPredicate pexp
						)
						| _ => [] 
					)
				| _ => []
		*)
				
		fun matchPF pat frame =
			let val vars = Frame.bind pat frame
			in
				Common.flap (fn (v, f) => 
					case f of 
						Frame.Fconstr (_, _, (_, Qvar (k, _))) => [(Predicate.PVar v, k)]
						| Frame.Fvar (a, (_, Qvar (k, _))) => [(Predicate.PVar v, k)]
						| Frecord ([], (_, Qvar (k, _))) => [(Predicate.PVar v, k)]
						| Frecord (fs, _) => 
							List.map (fs, fn (f, name) =>
								case f of 
									Frame.Fconstr (_, fls, (_, Qvar (k, _))) => (Predicate.Field (name, Predicate.PVar v), k)
									| _ => (print ("\nRecord ill typed " ^ (Frame.pprint f) ^ "\n"); assertfalse ())
							)
						| Fsum (_, fs, (_, Qvar (k, _))) => 
							Common.flap (fn (c, f) =>
	  							case f of 
	  								Frame.Fconstr (_, fs', (_, Qvar (k, _))) => 
	  									List.mapi (fs', fn (i, f') =>
	  										case f' of
	  											Fconstr (_, _, (subs, Qvar (k, _))) => 
	  												(Predicate.Proj (i+1, Predicate.Field (Con.toString c, Predicate.PVar v)), k)
	  											| Frame.Fvar (_, (_, Qvar (k, _))) =>
	  												(Predicate.Proj (i+1, Predicate.Field (Con.toString c, Predicate.PVar v)), k)
	  											| Frame.Fsum (_, _, (_, Qvar (k, _))) =>
	  												(Predicate.Proj (i+1, Predicate.Field (Con.toString c, Predicate.PVar v)), k)
	  											| _ => (print ("\nNested record " ^ (Frame.pprint frame) ^ "\n"); assertfalse ())
	  									)
	  								| _ => (print ("\nIllegal type " ^ (Frame.pprint frame) ^ "\n"); assertfalse ())
			  				) fs
			  			| Farrow (NONE, f1, f2) => 
			  				let val returnframe = Frame.getFrowFr f
			  					val paramvars = (*Frame.hofunFramevars frame (v)*) Frame.hofunFramevars_in_version_2 v frame
	  						in
	  							case returnframe of 
	  								Frame.Fconstr (_, _, (_, Qvar (k, _))) => 
	  									[(Predicate.FunApp ("P" ^ (Int.toString (List.length paramvars)), (Predicate.PVar v) :: paramvars), k)]
	  								| Frame.Fvar (_, (_, Qvar (k, _))) => 
	  									[(Predicate.FunApp ("P" ^ (Int.toString (List.length paramvars)), (Predicate.PVar v) :: paramvars), k)]
	  								| Frecord ([], (_, Qvar (k, _))) => []
	  								| Frame.Frecord (fs, _) =>
	  									List.map (fs, fn (f, n) =>
	  										case f of 
	  											Frame.Fconstr (_, _, (subs, Qvar (k, _))) => 
	  												(Predicate.Field (n, Predicate.FunApp ("P" ^ (Int.toString (List.length paramvars)), (Predicate.PVar v) :: paramvars)), k)
	  											| _ => (print ("\nNested construct " ^ (Frame.pprint returnframe) ^ "\n"); assertfalse ())
	  									)
	  								| _ => (print ("\nUnknow construct " ^ (Frame.pprint f) ^ "\n"); assertfalse ())
	  						end 
						| _ => [] 	
				) vars
			end
						
		(*
		 * precondition is called when path is verified as a true counterexample (only at modular level)
		 * backward traverse of the path collects the precondition under which the function call can avoid 
		 * the counterexample.
		 * @param exp the modular binding expression
		 * @param path the concrete path locations (for if-then-else only now)
		 * @param bindingframe the map of (pat, frame)
		 * @parame fenv from which we can find built-in function summary
		 * @param s the solution table from which function summary can be restored
		 * @return precondition in first order logic predicate form
		 *)
		fun precondition pred forwardexp exp path bindingframe fenv s freevars totalvars recflag fr envpending sri 
				funflag k_fun_pathup_precondition_table env force_convergence_flag = 
			let val _ = print "Generating precondition\n"
				val explist = ref []
				val _ = (visitingFlag := true)
				val exp = getFunctionBody exp
				val _ = visitExpForward dummypat forwardexp exp path explist false
				
				val li = List.rev (!explist)
				
				val _ = List.foreach (li, fn (cpat, cexp, expclass) =>
					case expclass of 
						ConditionalTrue => print ((CoreML.visitExp cexp) ^ " ==> \n") 
						| ConditionalFalse => print ((CoreML.visitExp cexp) ^ " ==> \n")
						| Assignment => print ((CoreML.Pat.visitPat cpat) ^ " = " ^ (CoreML.visitExp cexp) ^ "\n")
						| Selection => print ((CoreML.Pat.visitPat cpat) ^ " = " ^ (CoreML.visitExp cexp) ^ "\n")
				)
											
				fun genPrecondition pred explist bindingframe fenv s = 
					if (List.length (!explist) > 0 (*andalso (not force_convergence_flag)*)) then (
						let val (cpat, cexp, expclass) = List.pop explist
							val _ = print (" exp "^  (CoreML.visitExp cexp) ^ "\n\n") 
						in
							case (Exp.node cexp) of
							 	Exp.App (e1, e2) => (case (Exp.node e1) of
							 		Exp.Con _ => 
							 			let (*val _ = print ("\nKeeping backward. The orginal predicate is " ^ (Predicate.pprint pred) ^ "\n")*)
											val pred = pred_transform pred (cpat, cexp, expclass) bindingframe fenv s fr
											(*val _ = print ("\nThe transformed predicate is " ^ (Predicate.pprint pred) ^ "\n")*)
										in
						 					genPrecondition pred explist bindingframe fenv s
										end
							 		| _ =>
									let val (funname, funpat) = Constraintgen.getFunctioinAppPat cexp
										val funvar = Constraintgen.pat_var funpat
										(*val predvars = Constraintgen.pat_vars cpat*) 
									in
										if (HashTable.inDomain bindingframe funpat) then (* only two possibilities: skip this function or add a postcondition *)
											let val frame = (Lightenv.find (Constraintgen.pat_var funpat) env) handle Not_found
													=> (print ("\not in env for " ^ (Var.toString (Constraintgen.pat_var funpat)) ^ "\n"); 
													HashTable.lookup bindingframe funpat)
												(*val _ = print ("\nThe found frame is " ^ (Frame.pprint frame) ^ "\n")*)
												val returnframe = Frame.getFrowFr_rightversion frame		
												val pexprrefvarlist = matchPF cpat returnframe
											in	
												case (Pat.node cpat, returnframe) of 
													(Pat.Tuple _, Frecord (fs, (_, Qvar (refvar, _)))) =>
														if (List.exists (pexprrefvarlist, fn (pexpr, k) => 
																case (Predicate.containPexpr pexpr pred) of 
																	(true, _) => true
																	| _ => false 
														)) then
															let val vars = Frame.bind_index cpat returnframe
																val valu = Var.mk_ident ("V")
																val name = Var.mk_ident ("")
																val pred = List.fold (vars, pred, fn ((v, (f, index)), pred) =>
																	case index of 
																		SOME index => 
																			let val pred = Predicate.subst2 (Predicate.Field (index, (Predicate.PVar valu))) (Predicate.PVar v) pred
																			in pred end
																		| _ => (print "Error record frame\n"; assertfalse ())
																)
																val pred = (let val subs = genApplicationSubs (cexp) false frame
																	in Predicate.apply_substs subs pred end) handle RuntimeError => pred												
																
																val q = (name, valu, pred)
																val kqs = if (HashTable.inDomain s refvar) then HashTable.lookup s refvar else []
																val _ = HashTable.insert s (refvar, q :: kqs)
																val _ = List.foreach (q::kqs, fn q => print ("\n" ^ (Qualifier.pprint q) ^ "\n"))
																val _ = print ("\nGenerate postcondition for function " ^ 
																					(Pat.visitPat funpat) ^ " as " ^ (Predicate.pprint pred) ^ "\n")
															in (refvar, (q::kqs), SOME (Pat.var (funvar, Exp.ty e1)), li) end
														else genPrecondition pred explist bindingframe fenv s (* skip fun call *)
													| _ => (
														let val pexprrefvar = List.peek (pexprrefvarlist, fn (pexpr, k) => 
																case (Predicate.containPexpr pexpr pred) of 
																	(true, SOME _) => true
																	| _ => false
															) 
															val pexprrefvar = case pexprrefvar of 
																SOME (pexpr, k) => pexprrefvar
																| NONE => (
																	case (List.peek (pexprrefvarlist, fn (pexpr, k) =>
																		case (Predicate.containPexpr pexpr pred) of 
																			(true, _) => true
																			| _ => false
																	)) of
																		SOME (pexpr, k) => SOME (pexpr, k)
																		| NONE => NONE
																)	
														in 
															case pexprrefvar of 
																SOME (pexpr, refvar) =>  
																	let val _ = print ("\nStop backward. A postcondition instead of precondition is assumed on " ^ (Var.toString refvar) ^ ". \n")
																		val valu = Var.mk_ident ("V")
																		val name = Var.mk_ident ("")
																		val pred' = Predicate.subst2 (Predicate.PVar valu) pexpr pred
																 
																		val pred' = 
																			(let val subs = genApplicationSubs (cexp) false frame
																			in Predicate.apply_substs subs pred' end) handle RuntimeError => pred'												
																
																		val q = (name, valu, pred')
																		val kqs = if (HashTable.inDomain s refvar) then HashTable.lookup s refvar else []
																	in	
																		if (List.length kqs = 1) then case (List.first kqs) of
																				(_, _, Predicate.True) => (* We allow users of our tool to label a procedure that is not important *)
																					genPrecondition pred explist bindingframe fenv s 
																				| _ => (
																				let val _ = HashTable.insert s (refvar, q :: kqs)
																					val _ = List.foreach (q::kqs, fn q => print ("\n" ^ (Qualifier.pprint q) ^ "\n"))
																					val _ = print ("\nGenerate postcondition for function " ^ 
																						(Pat.visitPat funpat) ^ " as " ^ (Predicate.pprint pred') ^ "\n")
																				in (refvar, (q::kqs), SOME (Pat.var (funvar, Exp.ty e1)), li) end
																				)
																		else
																			let val _ = HashTable.insert s (refvar, q :: kqs)
																				val _ = List.foreach (q::kqs, fn q => print ("\n" ^ (Qualifier.pprint q) ^ "\n"))
																				val _ = print ("\nGenerate postcondition for function " ^ 
																							(Pat.visitPat funpat) ^ " as " ^ (Predicate.pprint pred') ^ "\n")
																			in (refvar, (q::kqs), SOME (Pat.var (funvar, Exp.ty e1)), li) end
																	end
																| NONE => (* skip this function call *)
																	genPrecondition pred explist bindingframe fenv s
														end
													)	
											end
										else
											let
												val _ = print ("\nKeeping backward. The orginal predicate is " ^ (Predicate.pprint pred) ^ "\n")
												val pred = pred_transform pred (cpat, cexp, expclass) bindingframe fenv s fr
												val _ = print ("\nThe transformed predicate is " ^ (Predicate.pprint pred) ^ "\n")
											in
							 					genPrecondition pred explist bindingframe fenv s
											end
									end
								)
								| _ => 
									let val _ = print ("\nKeeping backward. The orginal predicate is " ^ (Predicate.pprint pred) ^ "\n")
										val pred = pred_transform pred (cpat, cexp, expclass) bindingframe fenv s fr
										val _ = print ("\nThe transformed predicate is " ^ (Predicate.pprint pred) ^ "\n")
									in genPrecondition pred explist bindingframe fenv s end
						end
					)
					else (
						let val _ = print ("\nStop backward. Generate predcondition " ^ (Predicate.pprint pred) ^ "\n")
							val (pred, _) = Predicate.simplify_predicate pred
							val _ = print ("\nAfter simplification predicate is " ^ (Predicate.pprint pred) ^ "\n")
							val predvars = Predicate.vars pred 
							val (p, k, pred) = 
									(*if force_convergence_flag then (* recflag *)
									else*)
								let 
									val paramMap =
									HashTable.mkTable (hash_fn o (Predicate.pprint_pexpr), fn (a, b) => Predicate.logic_equals_pexp a b) (7, Not_found)
									val freevarMap = 
									HashTable.mkTable (hash_fn o (Predicate.pprint_pexpr), fn (a, b) => Predicate.logic_equals_pexp a b) (7, Not_found)
									val locallyrelatedfreevars = List.keepAllMap (HashTable.listItemsi freevars, fn (fv,_) => 
										if (List.exists (predvars, fn predvar => Var.equals (fv, predvar)) andalso HashTable.inDomain envpending fv) then ( 
											SOME (fv, HashTable.lookup envpending fv)
											)
										else NONE
									)
									val plist = analyzeFunFrame fr paramMap locallyrelatedfreevars envpending true
									val _ = print ("Observe plist\n")
									val _ = List.foreach (plist, fn p => (print ((Var.toString p) ^ ", ")))
									val _ = analyzeFunFrame fr freevarMap locallyrelatedfreevars envpending false 
									val funparampexps = List.map ((HashTable.listItemsi paramMap), (fn (a, b) => a))
									(*val funparampexps_fromfreevars = List.map ((HashTable.listItemsi freevarMap), (fn (a, b) => a))*) (*1*)
									val funparampexps = QuickSort.sortList (funparampexps, fn (fpe1, fpe2) =>
										let val fpv1 = List.first (Predicate.exp_vars fpe1)
											val fpv2 = List.first (Predicate.exp_vars fpe2)
											val index1 = List.index (plist, (fn pvar => Var.logic_equals (pvar, fpv1)))
											val index2 = List.index (plist, (fn pvar => Var.logic_equals (pvar, fpv2)))
											val index1 = case index1 of SOME i => i | NONE => 
												(print ("Internal frame error " ^ (Var.toString fpv1) ^ "\n"); assertfalse ())
											val index2 = case index2 of SOME i => i | NONE => 
												(print ("Internal frame error " ^ (Var.toString fpv2) ^ "\n"); assertfalse ())
										in
										 	if (index1 = index2) then case fpe1 of Predicate.PVar _ => false | _ => true
										 	else (index1 < index2) 
										end
									)
									val funparampexps = List.rev funparampexps
									val funparamvars = List.map (funparampexps, fn pe => List.first (Predicate.exp_vars pe))
									val funparamvars = List.removeDuplicates (funparamvars, Var.logic_equals)
									(*val funparamvars = List.map (funparampexps, fn pe => List.first (Predicate.exp_vars pe))
									val funparamvars = List.removeDuplicates (funparamvars, Var.logic_equals)
									val funparamvars = List.rev funparamvars
									val funparamvars = QuickSort.sortList (funparamvars, fn (var1, var2) => 
										let val str1 = Var.toString (var1)
											val str2 = Var.toString (var2)
											val index1 = Common.string_to_int (String.substring (str1, 2, (String.length str1)-2))
											val index2 = Common.string_to_int (String.substring (str2, 2, (String.length str2)-2))
										in (index1 <= index2) end
									)  *)
									(*val funparamvars_fromfreevars = List.map (funparampexps_fromfreevars, fn pe => List.first (Predicate.exp_vars pe))*) (*2*)
									val _ = List.foreach (funparampexps, fn v => print ((Predicate.pprint_pexpr v) ^ 
															"; its k is " ^ (Var.toString (HashTable.lookup paramMap v))))
									(*val _ = List.foreach (funparamvars_fromfreevars, fn v => print ((Var.toString v) ^ " "))*) (*3*)
									(*4*)
									val funparamMap = (*Common.mergeHashTable paramMap freevarMap*) paramMap
									val funpexps = (*funparampexps @ funparampexps_fromfreevars*) funparampexps
									val funvars = (*funparamvars @ funparamvars_fromfreevars*)  funparamvars
									val (pf) = Predicate.getFunversion pred funvars
									(* what is pf, pf is the higher order function P1 *)
									val (pe, k, pred) = case pf of 
										SOME pf => (
											(*let val (pf, pred) = case pf of 
												Predicate.FunApp (_, pef) => let val pf' = Predicate.FunApp ("P1", pef) in (pf', Predicate.subst2 pf' pf pred) end 
												| _ => (print "\nError with predicate of higher order function\n"; assertfalse ())
											in*)
												(pf, HashTable.lookup funparamMap pf, pred)
											(*end*)
										) (* Priority is given to higher order functions *)
										| NONE => 
											let val pexprrefvar = List.peek (funpexps, fn pexpr => 
													(* Then try first order constructs while priority is given to data structures *)
													case (Predicate.containPexpr pexpr pred) of 
														(true, SOME _) => true
														| _ => false
													) 
												val pexprrefvar = case pexprrefvar of 
													SOME pexpr =>  (pexprrefvar)
													| NONE => (														
														let val candidatelist = List.keepAll (funpexps, fn pexpr => 
																case (Predicate.containPexpr pexpr pred) of
																	(true, _) => true
																	| _ => false
																)
															val candidate = List.fold (candidatelist, NONE, fn (candidate, final) => 
																case final of 
																	NONE => SOME candidate
																	| SOME final' => 
																		let val p1 = List.first (Predicate.exp_vars final')
																			val p2 = List.first (Predicate.exp_vars candidate)
																		in
																			if (Predicate.pexpr_length final' < Predicate.pexpr_length candidate andalso (Var.logic_equals (p1, p2))) 
																			then SOME candidate else SOME final'
																		end
															)
														in
															case candidate of 
																SOME pexpr => SOME pexpr
																| NONE => NONE
														end
														
														(*
														case (List.peek (funpexps, fn pexpr =>
															case (Predicate.containPexpr pexpr pred) of 
																(true, _) => true
																| _ => false
														)) of
															SOME pexpr => SOME pexpr
															| NONE => NONE*)
														)
											in
												case pexprrefvar of 
													SOME pexpr => (pexpr, HashTable.lookup funparamMap pexpr, pred)
													| NONE => (
														(* We should really fist find if we can attach the predicate to contextual variable. NO. *)
														let val pe = List.first funparampexps
														in (pe, HashTable.lookup paramMap pe, pred) end	
													)											
											end
								in (pe, k, pred) end
							(*
							 * if funflag then only set ks to original pred and keeps the path up pred in a table (which is used for test generation)
							 * else set ks to the path pred.
							 *)
							val valu = Var.mk_ident ("V")
							val name = Var.mk_ident ("")
							(* Note: If it is recursive funtion, we discard the precondition *)
							fun recursivePreRemove pred = 
								case pred of 
									Predicate.Or (Predicate.Not pre, px') => 
										let val npx = recursivePreRemove px'
											val pre_vars = Predicate.vars pre
											(*val = getFunctionParams*)
										in
											if (Predicate.share pre npx orelse Predicate.containFunversion px') then Predicate.Or (Predicate.Not pre, npx)
											else (
												print ("\n::::cut " ^ (Predicate.pprint pred) ^ " to " ^ (Predicate.pprint npx) ^ "\n")
												;npx
											)
										end
									| _ => pred
							(*val pred = 
								if recflag then
									let val predslist = Predicate.andPredicateList pred
										val predslist = List.map (predslist, recursivePreRemove)
									in Predicate.big_and predslist end
								else pred*)
							val pred = Predicate.subst2 (Predicate.PVar valu) p pred
							val q = (name, valu, pred)
							val kqs = if (HashTable.inDomain s k) then HashTable.lookup s k else []
							(*val kqs = if (force_convergence_flag) then [] else kqs*)
						in
							(if funflag then
								HashTable.insert k_fun_pathup_precondition_table (k, q :: kqs)
							else
								HashTable.insert s (k, q :: kqs);
								print ("\nGenerate precondition  " ^ 
									" as " ^ (Predicate.pprint pred) ^ " for k " ^ (Var.toString k) ^ "\n");
								(* Set for chainlist of k1 *)
								let val ks = Constraint.getCurriedKs sri k
								in
									(*print "setting all ks for \n";*)
									List.foreach (ks, fn k => HashTable.insert s (k, q :: kqs))
									(*List.foreach (ks, fn k => print ((Var.toString k) ^ " "))*)
								end
							);
							(k, q::kqs, NONE, li)
						end
					)
			in genPrecondition pred explist bindingframe fenv s end
			
		(*
		 * postcondition is called when path is verified as a false counterexample (due to coarse modular
		 * abstraction of functions along the path)
		 * backward traverse of the path collects the postcondition of a function under which the couterexample
		 * can possibly be rejected.
		 * @param exp the modular binding expression 
		 * @param path the concrete path locations (for if-then-else only now)
		 * @param bindingframe the map of (pat, frame)
		 * @param fenv from which we can find built-in function summary
		 * @param s the solution map from which function summary can be restored
		 * @return (pat, postcondition, cpat) in which pat is for the newly asserted function, postcondition is in first order logic predicate form,
		 *	cpat is the unbounded variable in the future qualifier 
		 *)
		(* This function is discarded 
		fun postcondition pred forwardexp exp path bindingframe fenv s fr =
			let 
				val _ = print "Generating postcondition\n"
				val explist = ref []
				val _ = (visitingFlag := true)
				val exp = getFunctionBody exp
				val _ = visitExpForward dummypat forwardexp exp path explist true
				(*val _ = removeUnecessary explist*)
				(*val realfuns = List.map ((HashTable.listItemsi bindingframe), fn (a,b)=>a)*)
				
				fun genPostcondition pred explist =
					if (List.length (!explist) > 0) then
						let val (cpat, cexp, cexptype) = List.pop explist
							val _ = print ("\nexecuting statement cpat as " ^ (Var.toString (Constraintgen.pat_var cpat))
								^ " exp as " ^ (CoreML.visitExp cexp) ^ " \n")
							(* If cexp is a function application, we do the things:
				             * check if the function is virtual or real. 
				             * For virtual function, it is the function parameter of the current function and we are not aware of its function body now;
				             * We would not consider it as a source of false counterexample
				             * For real function, it is the one defined explicitly in the sml program and we can access to its function body now
				             * we consider it as the source of false counterexample and assert the postcondition for this function.
				             * However, the premise is that pred refers to the given pat
							 *)
							 exception exc
							 fun newPostcondition cpat cexp = case (Exp.node cexp) of
							 	Exp.App (e1, e2) =>
									let val (funname, funpat) = Constraintgen.getFunctioinAppPat cexp
										val funvar = Constraintgen.pat_var funpat
										val predvar = Constraintgen.pat_var cpat
									in
										if (HashTable.inDomain bindingframe funpat andalso Predicate.containVar predvar pred) then
											(* real function && predicate refers to pat; asserting pred as new post condition for this fun *)
											let val frame = HashTable.lookup bindingframe funpat
												val valu = Var.mk_ident ("V")
												val name = Var.mk_ident ("")
												val pred = Predicate.subst (Predicate.PVar valu) predvar pred
												val subs = genApplicationSubs (cexp) false frame
												val pred = Predicate.apply_substs subs pred												
												val refvar = getFrowRefVar frame
												val q = (name, valu, pred)
												val kqs = if (HashTable.inDomain s refvar) then HashTable.lookup s refvar else []
												val _ = HashTable.insert s (refvar, q :: kqs)
												val _ = print ("\nGenerate postcondition for function " ^ 
																	(Pat.visitPat funpat) ^ " as " ^ (Predicate.pprint pred) ^ "\n")
											in ((refvar, [q]), Pat.var (funvar, Exp.ty e1)) end
										else
											raise exc (* parameter fun call or unrefered real fun call *)
					 				end
							 	| _ => raise exc 
						in
							(let val (kqs, newpat) = newPostcondition cpat cexp
							in
								print ("Asserting a postcondition for function " ^ (Pat.visitPat newpat)); (kqs, newpat)
							end) handle exc => (
								let 
									val _ = print ("\nThe orginal predicate is " ^ (Predicate.pprint pred))
									val pred = pred_transform pred (cpat, cexp, cexptype) bindingframe fenv s fr
									val _ = print ("The transformed predicate is " ^ (Predicate.pprint pred))
								in
									genPostcondition pred explist
								end
							)
						end
					else (print "Error: cannot find a new postcondition for false counterexample"; assertfalse ())
			in
				genPostcondition pred explist
			end
			*)
	end