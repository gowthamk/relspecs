(* Author: He Zhu
 * From Computer Science Department
 * Purdue University 
 *
 * This file is the checker of SML program.
 * It assumes a ranked function call graph.
 *)

structure Modelcheck = 
	struct
		
		open CoreML
		open Common
		open HashTable
		open Frame

    structure Cs = Constraint
    structure RCs = RelConstraint
		
		type binding_id = int
		
		(*type binding_cnst = VerificationCondition.binding_cnst*)
		
		(* Modular top level bindings of sml program *)
		type binding_cnst = (* each for one binding including top level bindings and all the functions both toplevel or local *)
			{
				bid : binding_id, (* binding_id used for the function (binding) worklist *)
				pat : Pat.t, (* the name of the binding *)
				exp : Exp.t, (* the expression of the binding *)
				fr  : Frame.t, (* the frame of the binding *)
				sri : Constraint.ref_index, (* the constraints *)
			    ifb : (Var.t, Predicate.t) HashTable.hash_table
			}
		
		(* The worklist *)
		type binding_index =  
			{ 
				pats : (Pat.t, binding_id) hash_table, (* binding.pat --> binding_id*)
		  		orig : (binding_id, binding_cnst) hash_table, (* binding_id -> binding_cnst *)
		    	rank : (binding_id, (int * binding_id)) hash_table  (* id -> dependency rank *)
		    }
		
		(* The heap *)
		structure WH = Functional(
		    struct 
		    	(* each function has an unique id while we give each of them a rank (attached with name) *) 
		      	type t = binding_id * (int * binding_id) 
		      	fun compare (_, (i, id)) (_, (i', id')) = 
		      		if i <> i' then
		      			if i < i' then 1 else ~1
		      		else 
		      			case (Int.compare(id, id')) of
		      				  EQUAL => 0
		      				| LESS => 1
		      				| GREAT => ~1
		    end)
		
		val hash_fn = HashString.hashString
		
		fun pat_var pat = case (Pat.node pat) of Pat.Var var => var | _ => assertfalse ()
		fun pat_eq (pat1, pat2) = Var.logic_equals (pat_var pat1, pat_var pat2)
		
		(*
		 * 1. Given the call dependencies pat.t calls pat.t', generate the worklist.pats
		 * 2. Transform the call dependicies from pat.t -> pat.t to binding_id to binding_id
		 * 3. Generate worklist.rank
		 * 4. Generate the heap based on worklist.rank (call chain is obtainned )
		 * 5. Generate binding_cnst for each binding
		 *)
		
		val fresh_index = 
			let val i = ref 0
			in
		  		fn () => (incr i; !i)
			end		
		 
		(*
		 *@param (pat, exp) hash_table
		 *@return (pat, binding_id) hash_table 
		 *)
		fun gen_worklist_pats binding_table =
			let 
				val initial_size = 17
				val all_binding_names = (fn(a, b) => a) (List.unzip (HashTable.listItemsi binding_table))
				val pats = HashTable.mkTable (hash_fn o (Var.toString) o pat_var, pat_eq) (initial_size, Not_found)
			in
				List.foreach (all_binding_names, fn name => HashTable.insert pats (name, fresh_index())); pats
			end
						
			
		(* 
		 *@param callchain_list pat--> pat calls 
		 *@param pats (pat, binding_id) hash_table
		 *@return (binding_id, rank) hash_table
		 *)
		fun gen_callrank callchain_list pats = 
			let 
				val initial_size = 17
				val erm = HashTable.mkTable (hash_fn o (Int.toString), (op=)) (initial_size, Not_found)
				val callchain_list = (* (binding_id*binding_id) list *)
					Common.map_partial (fn (pat1, pat2) => (SOME (HashTable.lookup pats pat1, HashTable.lookup pats pat2)) 
						handle Common.Not_found => NONE) callchain_list
				val self_list = List.map (HashTable.listItemsi pats, fn (pat, bid) => (bid, bid))
				val callchain_list = List.append (callchain_list, self_list)
        (* callchain list is a DirectedGraph (not DAG) with vertices 
        identified by binding_id. *)
        (* scc_rank gives a DAG with each vertex as an SCC identified 
           by unique r *)
			in
				List.fold ((scc_rank callchain_list), erm, 
						(fn ((id, r), rm) =>  (HashTable.insert rm (id, (r, id)); rm)))
        (* binding_id id belongs to clique_id r *)
		    end
		    
		fun utilprint binding_table call_deps binding_frame = 
			(List.foreach (HashTable.listItemsi (binding_table), fn (pat, exp) => print ("pat: " ^ (Pat.visitPat pat) ^ " exp " ^ (visitExp exp) ^ "\n"));
			List.foreach (call_deps, fn (pat1, pat2) => print ("pat1 " ^ (Pat.visitPat pat1) ^ " pat2 " ^ (Pat.visitPat pat2) ^ "\n"));
			List.foreach (HashTable.listItemsi binding_frame, fn (pat, fr) => print ("pat " ^ (Pat.visitPat pat) ^ " fr " ^ (Frame.pprint fr) ^ "\n")))
		
		fun flatten_ho_fun fr var_binding = 
			let
				fun flatten_record pexp fr = case fr of
					Frame.Frecord (fs, _) =>
						List.foreach (fs, fn (f, name) => case f of 
							Frame.Frecord _ =>  flatten_record (Predicate.FunApp (name, [pexp])) f
							| Frame.Farrow _ => flatten_ho_fun_pexp (Predicate.FunApp (name, [pexp])) f 0
							| Frame.Fconstr (_, _, (subs, Frame.Qvar (k, _))) => HashTable.insert var_binding (k, Predicate.FunApp (name, [pexp]))
							| Frame.Fvar (a, (subs, Frame.Qvar (k, _))) => HashTable.insert var_binding (k, Predicate.FunApp (name, [pexp]))
							| _ => () 
						)
					| _ => (print "\nrecord not as record \n"; assertfalse ())
		
				and flatten_ho_fun_pexp' pexp fr = case fr of 
					Frame.Frecord _ => flatten_record pexp fr
					| Frame.Farrow _ => flatten_ho_fun_pexp pexp fr 0
					| Frame.Fconstr (_, _, (subs, Frame.Qvar (k, _))) => HashTable.insert var_binding (k, pexp)
					| Frame.Fvar (a, (subs, Frame.Qvar (k, _))) => HashTable.insert var_binding (k, pexp)
					| _ => ()
				
				and flatten_ho_fun_pexp pexp fr index = case fr of
					Frame.Farrow (_, f1, f2) =>
						let val _ = flatten_ho_fun_pexp' (Predicate.FunApp ("arg" ^ (Int.toString index), [pexp])) f1
						in case f2 of
							Frame.Farrow _ => flatten_ho_fun_pexp pexp f2 (index+1)
							| _ => ()
						end
					| _ => ()
				
				and flatten_ho_fun'' pat fr index = 
					let val varfrs = Frame.bind pat fr
					in 
						List.foreach (varfrs, fn (var, frame) =>
							case frame of 
								Frame.Frecord (fs, _) => flatten_record (Predicate.PVar var) frame
								| Frame.Farrow _ => flatten_ho_fun_pexp (Predicate.PVar var) frame 0
								| Frame.Fconstr (_, _, (subs, Frame.Qvar (k, _))) => HashTable.insert var_binding (k, Predicate.PVar var)
								| Frame.Fvar (a, (subs, Frame.Qvar (k, _))) => HashTable.insert var_binding (k, Predicate.PVar var)
								| _ => ()
						)
					end	
				and flatten_ho_fun' fr index = case fr of 
					Frame.Farrow (SOME ppat, f1, f2) => 
						let val _ = flatten_ho_fun'' ppat f1 index
						in
							case f2 of 
								  Frame.Farrow _ => flatten_ho_fun' f2 (index+1)
								| _ => ()
						end  
					| Frame.Farrow (_, f1, f2) => ()	
					| _ => ()
			in
				flatten_ho_fun' fr 0
			end
			
		(* 
		 * @param cs is the list of all the labeled constraints generated from sytax scan
		 * @param binding_table is all the pair of (pat, exp) pair
		 * @param call_deps is the list of call dependencies of (pat, pat) pair
		 * @param binding_frame is all the pair of (pat, frame) pair
		 *)
		fun make_binding_index cs binding_table call_deps binding_frame insidefunbindings postcondition_ks fenv = 
			let (*val _ = utilprint binding_table call_deps binding_frame
				val _ = print "\nall printed\n"*)
				val initial_size = 17
        (* fbs is binding -> constraint map *)
				val fbs = HashTable.mkTable (hash_fn o Var.toString o pat_var, pat_eq) (initial_size, Not_found)
				(* lc_binding is belong_pat of the expression for which this constraing was generated *)
        (* collect all constraints for a belong_pat *)
				val _ = List.foreach (cs, fn (c as (Constraint.lc {lc_binding = binding, ...})) => 
          (print ("constraint for binding : "^(CoreML.Pat.visitPat binding)^" found\n");
					case HashTable.find fbs binding of 
					  	  SOME l => HashTable.insert fbs (binding, (List.append (l, [c]))) 
						| NONE => HashTable.insert fbs (binding, [c])))		
				val orig' = HashTable.mkTable (hash_fn o (Int.toString), (op=)) (initial_size, Not_found)
        (* pats' is pat -> binding_id table *)
				val pats' = gen_worklist_pats binding_table
				val _ = print "pats generated.\n"
        (* rank' is binding_id -> (scc_rank,binding_id) map *)
				val rank' = gen_callrank call_deps pats'
				val _ = print "rank generated.\n"
			in
				List.foreach ((HashTable.listItemsi fbs), fn (bpat, lcs)=> 
					let 
						val bid' = HashTable.lookup pats' bpat
						val exp' = HashTable.lookup binding_table bpat
						val fr' = HashTable.lookup binding_frame bpat
						val sri' = Constraint.split_lcs lcs postcondition_ks
						
						
						fun isRecursiveFun bodyExp funvar = 
							let val recflag = ref false
							in
								(Exp.foreachVar (bodyExp, (fn mvar => if Var.logic_equals(mvar, funvar) 
																	then recflag := true 
																	else ())
								); !recflag)
							end
						val recflag = isRecursiveFun exp' (Constraintgen.pat_var bpat)
						
						(* dealing with insidefunbindings. The goal is to relate a higher order predicate to a higher order value binding *)
						val insidefunbinding = HashTable.mkTable (hash_fn o (Var.toString), Var.logic_equals) (17, Not_found) 
						val _ = if (HashTable.inDomain insidefunbindings bpat) then
									let val ifbs = HashTable.lookup insidefunbindings bpat
									in
										List.foreach (ifbs, fn (pat, exp) => 
											case (Exp.node exp) of
												Exp.App _ => (
													let val (funname, funpat) = Constraintgen.getFunctioinAppPat exp
														val (funvar, funty) = Constraintgen.getFunctionApp exp
														val patvar = Constraintgen.pat_var pat
													in 
														if (HashTable.inDomain binding_frame funpat orelse Lightenv.mem funvar fenv) then ((* this is named function not higher order function *)
															let val patty = CoreML.Pat.ty pat
																val funfr = if (HashTable.inDomain binding_frame funpat) then HashTable.lookup binding_frame funpat
																			else Lightenv.find funvar fenv
															in
																if (Type.isArrow patty) then 
																	case (Frame.getFrowFr_rightversion funfr) of
																		Frame.Farrow _ => ()
																		| _ => (* Supposed not to be a return function but indeed is so is higher order function *) (
																			HashTable.insert insidefunbinding (patvar, Predicate.True)
																		)
																else () 
															end
														)
														else ( (* This is considered as higher order function *)
															let val patty = CoreML.Pat.ty pat
															in
																if (Type.isArrow patty) then 
																	let val pred_leftpart = 
																			(*if (Type.isArrow patty) then*)
																				let val pvs = VerificationCondition.ho_args_fromty (Type.toMyType patty) (patvar)
																				in Predicate.FunApp ("P" ^ (Int.toString (List.length pvs)), (Predicate.PVar patvar) :: pvs) end
																			(*else Predicate.PVar patvar*)
																		val pred_rightpart = 
																			let val pvs = VerificationCondition.ho_args_fromty (Type.toMyType funty) (funvar)
																			in Predicate.FunApp ("P" ^ (Int.toString (List.length pvs)), (Predicate.PVar funvar) :: pvs) end
																			
																		val temp_leftpart_var = Var.fromString "temp@@"
																		val pred = Predicate.Atom (Predicate.PVar temp_leftpart_var, Predicate.Eq, pred_rightpart)
																		
																		val subs = BackwardTraverse.genApplicationSubsByType exp (Type.toMyType funty) 0
																		val pred = Predicate.apply_substs subs pred 
																		
																		val pred = Predicate.subst pred_leftpart temp_leftpart_var pred
																	in HashTable.insert insidefunbinding (patvar, pred) end
																(*else if recflag then (
																	
																)*)
																else (
																	let fun paramIndex e = case (Exp.node e) of
														      				Exp.Var _ => ((~1), [])
														      				| Exp.App (e1, e2) => 
														      					let val (index, pvs) = paramIndex e1  
														      					in case (Exp.node e2) of
														      						Exp.Var (var, _) =>  
																      					(1+index, pvs @ 
																	      					[Predicate.Atom (Predicate.FunApp ("arg" ^ (Int.toString (1+index)), [Predicate.PVar funvar]), 
							 																	Predicate.Eq, Predicate.PVar (var()))]
																      					) 
																      				| Exp.Record r => (
																      					if (Vector.length (Record.toVector r) = 0) then
																      						(1+index, pvs @ 
																	      					[Predicate.Atom (Predicate.FunApp ("arg" ^ (Int.toString (1+index)), [Predicate.PVar funvar]), 
							 																	Predicate.Eq, Predicate.PVar (Var.fromString "dummy"))]
																      						) 
																      					else (1+index, pvs)
																      				)
														      						| _ => (1+index, pvs) 
														      					end							      					
														      				| _ => (print "\nError function form\n"; assertfalse ())
														      			val (_, preds) = paramIndex exp
																	in
																		if (List.length preds <> 0) then
																			HashTable.insert insidefunbinding (patvar, Predicate.big_and preds)
																		else ()
																	end
																)
															end
														)
													end handle RuntimeError => ())
												| _ => print ("\nnon app exp in insidefunbindings\n"; assertfalse ()) (* we will not add non app expression into insidefunbindings at this time *)
										)
									end
								else ()
					in
						HashTable.insert orig' (bid', {bid = bid', pat = bpat, exp = exp', fr = fr', sri = sri', ifb=insidefunbinding})
					end)
				;
				{pats = pats', orig = orig', rank = rank'}
			end
			
		(* Push a binding into the worklist *)
		fun push_worklist sbi w pats =
			List.fold (pats, w, fn (pat, w) =>
				let val id = HashTable.lookup (#pats sbi) pat
					val _ = print ("@[Pushing binding@" ^ (Int.toString id) ^ "@\n@]")
				in
					WH.add (id, (HashTable.lookup (#rank sbi) id)) w
				end
			)
			
		fun push_worklist_byid sbi w ids = 
			List.fold (ids, w, fn (id, w) =>
				WH.add (id, (HashTable.lookup (#rank sbi) id)) w
			)
						
		(* Pop a binding out of the worklist *)
		fun pop_worklist sbi w =
			(let val id = (fn (a, b) => a) (WH.maximum w)
			in				
				(SOME (id, (HashTable.lookup (#orig sbi) id)), WH.remove w) handle Not_found => (print "Not found in #orig for this id\n"; assertfalse ())
			end)
			handle WH.EmptyHeap => (NONE, w)
		
		(*
		 * Put all the functions into a heap based on the weight of their call dependencies
		 *)
		fun make_initial_worklist sbi = 
			let val pats = ((fn (a, b) => a) o List.unzip o HashTable.listItemsi) (#pats sbi)
			in
				push_worklist sbi WH.empty pats
			end
		
		fun analyzeFunFrame fr paramMap = 
			let fun analyzeFunFrame'' pat fr = 
					let val varfrs = Frame.bind pat fr
					in List.foreach (varfrs, fn (var, frame) =>
				  			case frame of 
				  				Fconstr (_, fs, (subs, Qvar (k, _))) => (
				  					HashTable.insert paramMap (Predicate.PVar var, k);
				  					(* A non emplty list of fs means the built-in datatypes, such as list ... *)
				  					if (List.length fs = 0) then ()
				  					else if (List.length fs = 1) then (
				  						case (List.first fs) of
				  							Fconstr (_, _, (_, Qvar (k, _))) => HashTable.insert paramMap (Predicate.Field ("ele", Predicate.PVar var), k) 
				  							| Frecord (_, (_, Qvar (k, _))) => HashTable.insert paramMap (Predicate.Field ("ele", Predicate.PVar var), k)
				  							| Fvar (_, (_, Qvar (k, _))) => HashTable.insert paramMap (Predicate.Field ("ele", Predicate.PVar var), k)
				  							| _ => ()
				  					) else ()
				  				)
				  				| Farrow _ => 
			  						let val returnframe = Frame.getFrowFr frame
			  							val paramvars = (*Frame.hofunFramevars frame (var)*) Frame.hofunFramevars_in_version frame
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
				  				| Frecord (fs, _) => 
			  						List.foreach (fs, fn (f, name) => 
			  							case f of 
			  								Frame.Fconstr (_, _, (_, Qvar (k, _))) => 
			  									HashTable.insert paramMap (Predicate.Field (name, Predicate.PVar var), k)
			  								| Frame.Fvar (_, (_, Qvar (k, _))) =>
			  									HashTable.insert paramMap (Predicate.Field (name, Predicate.PVar var), k)
			  								| Frame.Fsum (_, _, (_, Qvar (k, _))) =>
			  									HashTable.insert paramMap (Predicate.Field (name, Predicate.PVar var), k)
			  								| _ => (print ("\nNested record " ^ (Frame.pprint frame) ^ "\n"); assertfalse ())
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
				 					Farrow _ => (plist @ (analyzeFunFrame' f2 paramMap))
				 					| _ => plist
							end  	
						| Farrow (_, f1, f2) => [] (* the function of the frame returns a function *)
						| _ => (print ("Error: In analyzeFunFrame ill function frame" ^ (Frame.pprint fr)); assertfalse ())
			in analyzeFunFrame' fr paramMap end
		
		fun setInvariant pred fr sri s pre postcondition_ks = 
			if (pre) then
				let val (p, k) =
						let val paramMap =
							HashTable.mkTable (hash_fn o (Predicate.pprint_pexpr), fn (a, b) => Predicate.logic_equals_pexp a b) (7, Not_found)
							val plist = analyzeFunFrame fr paramMap 
							val funparampexps = List.map ((HashTable.listItemsi paramMap), (fn (a, b) => a))
							
							val funparampexps = QuickSort.sortList (funparampexps, fn (fpe1, fpe2) =>
								let val fpv1 = List.first (Predicate.exp_vars fpe1)
									val fpv2 = List.first (Predicate.exp_vars fpe2)
									val index1 = List.index (plist, fn p => (Var.logic_equals (p, fpv1)))
									val index2 = List.index (plist, fn p => (Var.logic_equals (p, fpv2)))
									val index1 = case index1 of SOME i => i | NONE => (print "Internal frame error-model check\n"; assertfalse ())
									val index2 = case index2 of SOME i => i | NONE => (print "Internal frame error-model check\n"; assertfalse ())
								in (index1 <= index2) end
							)
							val funparampexps = List.rev funparampexps
							val funparamvars = List.map (funparampexps, fn pe => List.first (Predicate.exp_vars pe))
							val funparamvars = List.removeDuplicates (funparamvars, Var.logic_equals)
							
							val (pf) = Predicate.getFunversion pred funparamvars
							(* what is pf, pf is the higher order function P1 *)
							val (pe, k) = case pf of 
								SOME pf => (pf, HashTable.lookup paramMap pf) (* Priority is given to higher order functions *)
								| NONE => 
									let val pexprrefvar = List.peek (funparampexps, fn pexpr => 
											(* Then try first order constructs while priority is given to data structures *)
											case (Predicate.containPexpr pexpr pred) of 
												(true, SOME _) => true
												| _ => false
											) 
										val pexprrefvar = case pexprrefvar of 
											SOME pexpr =>  pexprrefvar
											| NONE => (
												let val candidatelist = List.keepAll (funparampexps, fn pexpr => 
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
											
												(*case (List.peek (funparampexps, fn pexpr =>
													case (Predicate.containPexpr pexpr pred) of 
														(true, _) => true
														| _ => false
												)) of
													SOME pexpr => SOME pexpr
													| NONE => NONE*)
												)
									in
										case pexprrefvar of 
											SOME pexpr => (pexpr, HashTable.lookup paramMap pexpr)
											| NONE => (
												let val pe = List.first funparampexps
												in (pe, HashTable.lookup paramMap pe) end	
											)											
									end
						in
							(pe, k) 
						end
				
					val valu = Var.mk_ident ("V")
					val name = Var.mk_ident ("")
					
					val pred = Predicate.subst2 (Predicate.PVar valu) p pred
					val q = (name, valu, pred)
					val kqs = if (HashTable.inDomain s k) then HashTable.lookup s k else []
					val _ = print ("\nthe post ks is listed below: \n")
											val _ = List.foreach (HashTable.listItemsi postcondition_ks, fn (k,_) => print ((Var.toString k) ^ " "))
				in (
					HashTable.insert s (k, q :: kqs);
					print ("\nInsert precondition  " ^ 
						" as " ^ (Predicate.pprint pred) ^ " for k " ^ (Var.toString k) ^ "\n");
					(* Set for chainlist of k1 *)
					let val ks = Constraint.getCurriedKs sri k
					in
						List.foreach (ks, fn k => 
							if (HashTable.inDomain postcondition_ks k) then ()
							else HashTable.insert s (k, q :: kqs))
					end)
				end
			else (
				(* set post condition *)
				let val returnframe = Frame.getFrowFr fr
					val v = Var.fromString "AA"
					val pexprrefvarlist = case returnframe of 
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
	  											| _ => (print ("\nNested record " ^ (Frame.pprint returnframe) ^ "\n"); assertfalse ())
	  									)
	  								| _ => (print ("\nIllegal type " ^ (Frame.pprint returnframe) ^ "\n"); assertfalse ())
			  				) fs
						| _ => []		
					
					
					val _ = print ("\nPred is " ^ (Predicate.pprint pred) ^ "\n")
					val _ = List.foreach (pexprrefvarlist, fn (pexpr, k) =>
						print ("\npexpr: " ^ (Predicate.pprint_pexpr pexpr) ^ " k is " ^ (Var.toString k) ^"\n")
					)
					
					val pexprrefvar = List.peek (pexprrefvarlist, fn (pexpr, k) => 
						case (Predicate.containPexpr pexpr pred) of 
							(true, SOME _) => true
							| _ => false
					) 
					
					val pexprrefvar = case pexprrefvar of 
						SOME (pexpr, k) =>  pexprrefvar
						| NONE => (
							case (List.peek (pexprrefvarlist, fn (pexpr, k) =>
								case (Predicate.containPexpr pexpr pred) of 
									(true, _) => true
									| _ => false
							)) of
								SOME (pexpr, k) => SOME (pexpr, k)
								| NONE => NONE
						)	
						
					val _ = print ("\nthe post ks is listed below: \n")
											val _ = List.foreach (HashTable.listItemsi postcondition_ks, fn (k,_) => print ((Var.toString k) ^ " "))
				in 
					case pexprrefvar of 
						SOME (pexpr, refvar) =>  
							let val _ = print ("\nAdd post condition on " ^ (Var.toString refvar) ^ ". \n")
								val valu = Var.mk_ident ("V")
								val name = Var.mk_ident ("")
								val pred = Predicate.subst2 (Predicate.PVar valu) pexpr pred										
						
								val q = (name, valu, pred)
								val _ = print ("\nto be added qualifier is " ^ (Qualifier.pprint q) ^ "\n")
								val kqs = if (HashTable.inDomain s refvar) then HashTable.lookup s refvar else []
								val _ = HashTable.insert s (refvar, q :: kqs)
								val ks = Constraint.getCurriedKs sri refvar
							in  
								List.foreach (ks, fn k => 
									if (HashTable.inDomain postcondition_ks k) then
										(print ("curried setting on " ^ (Var.toString k) ^ "\n"); HashTable.insert s (k, q :: kqs))
									else ()
								)
							end
						| NONE => (case pred of
							 Predicate.True => List.foreach (pexprrefvarlist, fn (pexpr, k) => HashTable.insert s (k, [(Var.mk_ident ("V"), Var.mk_ident (""), pred)])) 
							 | _ => (print ("\nCannot understand given post invariant\n"); assertfalse ())
						)
				end
			)
		(*
		 * Intially abstracting all functions into true arrow true
		 * @param sbi is the indexed constraints (types show above)
		 * @return solution map than will be used during iterative verification
		 *)      		
		fun make_initial_solution sbi binding_frame binding_table postcondition_ks invariants =
			let 
				val initial_size = 17
				val s = HashTable.mkTable (hash_fn o (Var.toString), Var.logic_equals) (initial_size, Not_found)
				val _ = List.foreach (HashTable.listItemsi (binding_frame), fn (pat, fr) => 
							let val ty = Pat.ty pat
							in 
								(if (Type.isArrow ty) then
									let val id = HashTable.lookup (#pats sbi) pat
										val sri = #sri (HashTable.lookup (#orig sbi) id)
									in
										List.foreach (Frame.arrowframe_refinement_vars fr, fn var => (
											print ("\nAbstracting var " ^ (Var.toString var)); HashTable.insert s (var, [])
											; List.foreach (Constraint.getCurriedKs sri var, fn k' => (
												print ("\nAlso Abstracting curried variable " ^ (Var.toString k'));
												if (HashTable.inDomain postcondition_ks k') then (print ("\nnot setting"))
												else (print ("\nCurried setting this var"); HashTable.insert s (k', []))	)
											  )
										))
									end
								else (List.foreach (Frame.refinement_vars fr, fn var => 
										(print ("\nAbstracting var " ^ (Var.toString var)); HashTable.insert s (var, []))
								)))
							end)
				val _ = List.foreach (invariants, fn (vi, vf, ip) =>
					let val fpat = Pat.var (vf, Type.var(Tyvar.newNoname {equality = false}))
						val _ = print ("\nInvaraint for function " ^ (Var.toString vf) ^ "\n")
					in
						if (HashTable.inDomain binding_frame fpat) then
							let val fr = HashTable.lookup binding_frame fpat
								val id = HashTable.lookup (#pats sbi) fpat
								val sri = #sri (HashTable.lookup (#orig sbi) id)
								val exp = HashTable.lookup binding_table fpat
								val matching_subs = ref []
								val _ = BackwardTraverse.getFunctionParams (BackwardTraverse.getFunctionBody exp) matching_subs
								(*val matching_subs = List.map (!matching_subs, fn (vx, vy) => (vy, Predicate.PVar vx))*)
								val ip = Predicate.apply_substs (!matching_subs) ip
								val ips = Predicate.andPredicateList ip
								val _ = List.foreach (ips, fn ip => (print ((Predicate.pprint ip) ^ "\n")))
							in	
								List.foreach (ips, fn ip => setInvariant ip fr sri s (String.hasPrefix (Var.toString vi, {prefix="pre"})) postcondition_ks)
							end
						else (print "\nError unknow function\n")
					end
				)
				val _ = print "\nThe intial abstraction is shown below\n"
				val _ = 
					List.foreach (HashTable.listItemsi binding_frame, fn (a, b) => print (
			  		 (Var.toString (Constraintgen.pat_var a)) ^ " : " ^
			  		 (Frame.pprint_final b (Constraint.solution_map s)) ^ "\n")
			  		 )
			in s end 
		
		(* 
		 * Verification of a modular binding
		 * @param binding_cnst is {bid, pat, exp, constraint.sri} for a binding which is either function (both toplevel or local) or toplevel binding
		 * @return int value:
		 * 	true: verified
		 *  true: not verified with real counterexample (only in this modular binding level), the precondition is inferred
		 *  false: not verified with false counterexample, both this moduar binding and the called function int it should be inserted into the worklist
		 *)		
		 
		fun verify s back_s procedureflag bcnst w' binding_frame paths fenv decs freevars totalvars 
				var_frame frame_vars hov force_convergence_table non_convergence_table polymatching_table parameterIndex_table =
			let 
				val (vcr, pat, kqs, cid, exp) = VerificationCondition.verify bcnst s back_s procedureflag binding_frame paths fenv decs freevars totalvars 
						var_frame frame_vars hov force_convergence_table non_convergence_table polymatching_table parameterIndex_table
			in
				(vcr, pat, kqs, cid, exp)
			end 
			
		val result = ref false
		
		(* recording the procedures that should support current verifying procedure *)
		val pending_procedures = HashTable.mkTable (hash_fn o Int.toString, (op=)) (11, Not_found) 
		
		val curr_procedure = ref (~1)
			 		
		fun iterate_verify sbi s back_s w binding_frame paths fenv decs freevars totalvars call_deps 
				var_frame frame_vars hov force_convergence_table non_convergence_table polymatching_table parameterIndex_table postcon_non_cvg_table = 
	  		case (pop_worklist sbi w) of
	  			  (NONE, _) => !result
	  			| (SOME (id, bcnst), w') => 
	  				let (* see if this procecdure is in the pendding procedure or if current verifying procdure or if a new procedure encountered
	  				     * We use 0 --> pending procedure
	  				     *    use 1 --> verifying procedure
	  				     *    use 2 --> new procedure
	  				     *)
	  				    
	  				    val procedure_flag = 
	  				    	if (HashTable.inDomain pending_procedures id) then 0
	  				    	else if (id = (!curr_procedure)) then 1
	  				    	else (
	  				    		curr_procedure := id;
	  				    		2
	  				    	)				
	  					val (r, id) = HashTable.lookup (#rank sbi) (#bid bcnst)
	  					val fname = Constraintgen.pat_var (#pat bcnst)	
	  					val _ = print "\n*************************************\n"
	  					val _ = print ("@[Verifying:@ " ^ (Var.toString fname) ^ " with rank of " ^ (Int.toString r) ^ "):@]")
	  					val _ = print "\n*************************************\n"
	  					val _ = HashTable.clear force_convergence_table
	  					val (verify_result, tobeadded_pat, kqs, cid, exp) = verify s back_s (procedure_flag = 1 orelse procedure_flag = 2) 
	  								bcnst w' binding_frame paths fenv decs freevars totalvars 
	  								var_frame frame_vars hov force_convergence_table non_convergence_table polymatching_table parameterIndex_table
	  					val w' = case (tobeadded_pat, kqs, cid, exp) of 
	  						(NONE, NONE, _, _) => if (verify_result) then w' else (print "\nError ending the function verification\n"; assertfalse ())
	  						| (NONE, SOME kls, SOME cid, SOME exp) => 
	  							if (verify_result) then (print "\nError continuing the function verification\n"; assertfalse ()) 
	  							else (
	  								if (not (HashTable.inDomain postcon_non_cvg_table (#pat bcnst, cid)) orelse ((HashTable.lookup postcon_non_cvg_table (#pat bcnst, cid)) < 10)) then 
	  								let val _ = 
		  									if (HashTable.inDomain postcon_non_cvg_table (#pat bcnst, cid)) then
		  										HashTable.insert postcon_non_cvg_table ((#pat bcnst, cid), (HashTable.lookup postcon_non_cvg_table (#pat bcnst, cid))+1)
		  									else HashTable.insert postcon_non_cvg_table ((#pat bcnst, cid), 0)
		  								val _ = print ("\nObserved the pat is " ^ (Var.toString (pat_var (#pat bcnst))) ^ " the cid is " ^ (Int.toString cid) ^ "\n")
	  									val _ = print ("\nObserved the ci is " ^ (Int.toString (HashTable.lookup postcon_non_cvg_table (#pat bcnst, cid))) ^ "\n")
	  									val cache = HashTable.mkTable (hash_fn o Var.toString o pat_var, pat_eq) (11, Not_found)
	  									val nw = List.fold (call_deps, w', fn ((pat1, pat2), nw) =>
		  								let	val var1 = Constraintgen.pat_var pat1
		  									(*val _ = print ("\n" ^ (Var.toString var1) ^ " calls ")
		  									val _ = print ((Var.toString (Constraintgen.pat_var pat2)) ^ "\n")*)
		  									val var2 = fname
		  								in
		  									if (Var.logic_equals (var1, var2) andalso (HashTable.inDomain binding_frame pat2)
		  										andalso (not (HashTable.inDomain cache pat2))
		  										andalso (not (pat_eq (#pat bcnst, pat2)))) then
		  										(print ("\npushing " ^ (Var.toString (Constraintgen.pat_var pat2)) ^ "into heap to reverify\n");
		  										HashTable.insert cache (pat2, ());
		  										
		  										let val toid = HashTable.lookup (#pats sbi) pat2
				  									val sri = #sri (HashTable.lookup (#orig sbi) toid)
				  								in
				  									List.foreach (kls, fn (k, qs) =>
														let val ks = Constraint.getCurriedKs sri k
														in
															(*print "\nthe curried ks is listed below: \n";
															List.foreach (ks, fn k => print ((Var.toString k) ^ " "));*)
															List.foreach (ks, fn k => HashTable.insert s (k, qs))
														end
													)
												end;
												let val p_id = HashTable.lookup (#pats sbi) pat2
												in HashTable.insert pending_procedures (p_id, ()) end;
		  										push_worklist sbi nw [pat2])
		  									else nw
		  								end)
		  							in push_worklist_byid sbi nw [id] end
		  							else w'
	  							)
	  						| (SOME p, SOME kls, SOME cid, _) => (
	  							if (not (HashTable.inDomain postcon_non_cvg_table (p, cid)) orelse ((HashTable.lookup postcon_non_cvg_table (p, cid)) < 10)) then
		  							let val _ = print 
		  									("\nWill add new function to the top of fun heap which is " ^ (Var.toString (Constraintgen.pat_var p)) ^ "\n")
		  								val _ = 
		  									if (HashTable.inDomain postcon_non_cvg_table (p, cid)) then
		  										HashTable.insert postcon_non_cvg_table ((p, cid), (HashTable.lookup postcon_non_cvg_table (p, cid))+1)
		  									else HashTable.insert postcon_non_cvg_table ((p, cid), 0)
		  								val nw = push_worklist sbi w' [p]
		  								val p_id = HashTable.lookup (#pats sbi) p
		  								val _ = HashTable.insert pending_procedures (p_id, ())
		  								val cache = HashTable.mkTable (hash_fn o Var.toString o pat_var, pat_eq) (11, Not_found)
		  								val nw = List.fold (call_deps, nw, fn ((pat1, pat2), nw) =>
		  								let val var1 = Constraintgen.pat_var pat1
		  									val _ = print ("\n" ^ (Var.toString var1) ^ " calls ")
		  									val var2 = Constraintgen.pat_var p
		  									val _ = print ((Var.toString (Constraintgen.pat_var pat2)) ^ "\n")
		  								in
		  									if (Var.logic_equals (var1, var2) andalso (HashTable.inDomain binding_frame pat2)
		  										andalso (not (HashTable.inDomain cache pat2))
		  										andalso (not (pat_eq (p, pat2)))) then
		  										(print ("\npushing " ^ (Var.toString (Constraintgen.pat_var pat2)) ^ "into heap to reverify\n");
		  										HashTable.insert cache (pat2, ());
		  										let val p_id = HashTable.lookup (#pats sbi) pat2
		  										in HashTable.insert pending_procedures (p_id, ()) end;
		  										push_worklist sbi nw [pat2])
		  									else nw
		  								end
		  								)
		  								val _ = print "\nFunction added to heap already\n"
		  								
		  								(* Set for chainlist of k1 *)
		  								val toid = HashTable.lookup (#pats sbi) p
		  								val sri = #sri (HashTable.lookup (#orig sbi) toid)
		  								val _ = List.foreach (kls, fn (k, qs) =>
											let val ks = Constraint.getCurriedKs sri k
											in
												print "\nthe curried ks is listed below: \n";
												List.foreach (ks, fn k => print ((Var.toString k) ^ " "));
												List.foreach (ks, fn k => HashTable.insert s (k, qs))
											end
										) 
															
		  							in 
		  								(*if (pat_eq ((#pat bcnst), p)) then nw
		  								else*) push_worklist_byid sbi nw [id] 
		  							end
	  							else w')
	 						| _ => (print "\nill-returned kqs\n"; assertfalse ())
	 				in
	 					print ("Verifying reult of function " ^ (Var.toString fname) ^" is " ^ (Bool.toString verify_result) ^ "\n");
	 					result := verify_result;
	 					(* if the verification result is true and this is current verifying procedure, 
	 					 * we should recover our solution back to the weaskest one *)
	 					if (verify_result) then 
	 						if (procedure_flag = 2) then (* new procedure directly verified, this is good. We have nothing to do. *) () 
	 						else if (procedure_flag = 1)  then (* finally current verifying procedure is verified, recover all pending procedure spec back *) (
	 							(* s ----> back_s: update s according to the element in update_s *)
	 							HashTable.modifyi (fn (k, _) =>
									(HashTable.lookup back_s k) handle Not_found => ([])  
								) s 
	 						)
	 						else (* pending procedure is verified *) HashTable.remove pending_procedures id
	 					else (
							(* At this step, pending procedure and current verifying procedure are already pushed in.*) 					
	 					);	
	 					
	 					iterate_verify sbi s back_s w' binding_frame paths fenv decs freevars totalvars call_deps 
	 						var_frame frame_vars hov force_convergence_table non_convergence_table polymatching_table parameterIndex_table postcon_non_cvg_table
	    			end
		    
		
		fun closurevars decs fenv = 
			let 
				val boundedvars = HashTable.mkTable (MLton.hash, Var.equals) (17, Common.Not_found)
				val totalvars = HashTable.mkTable (MLton.hash, Var.equals) (17, Common.Not_found)	
				val freevars = HashTable.mkTable (MLton.hash, Var.equals) (17, Common.Not_found)
				val dummy_fr = Frame.Fvar (Var.fromString "dummy_which_should_be_replaced", Frame.empty_refinement)
				fun loopDec flag boundedvars functionpat d =
			       case d of
			          Dec.Datatype _ => d
			        | Dec.Exception _ => d
			        | Dec.Fun {decs, tyvars} => 
			        	(Vector.foreach (decs, fn dec => (HashTable.insert boundedvars ((#var dec), ()); HashTable.insert totalvars ((#var dec), (dummy_fr, 0))));
			        	let
			        		val newboundedvars = HashTable.mkTable (MLton.hash, Var.equals) (17, Common.Not_found)
			        		val decs' = Vector.map (decs, fn dec => {lambda=loopLambda flag newboundedvars (#var dec) (#lambda dec), var=(#var dec)})
			        	in
			        		Dec.Fun {decs=decs', tyvars=tyvars}
			        	end)
			        | Dec.Val {rvbs, vbs, nonexhaustiveExnMatch, nonexhaustiveMatch, tyvars} =>
			        	(Vector.foreach (rvbs, fn rvb => (HashTable.insert boundedvars ((#var rvb), ()); HashTable.insert totalvars ((#var rvb), (dummy_fr, 0))));
			        	Vector.foreach (vbs, fn pattern => 
			        		Pat.foreachVar ((#pat pattern), fn v => (HashTable.insert boundedvars (v, ()); HashTable.insert totalvars (v, (dummy_fr, 0)))));
			        	let
			        		val newboundedvars = HashTable.mkTable (MLton.hash, Var.equals) (17, Common.Not_found)			        	
			        		val rvbs' = Vector.map (rvbs, fn rvb => {lambda=loopLambda flag newboundedvars (#var rvb) (#lambda rvb), var=(#var rvb)}); 
			        		val vbs' = Vector.map (vbs, fn vb => {exp=loop flag boundedvars functionpat (#exp vb),
                             lay=(#lay vb),
                             nest=(#nest vb),
                             pat=(#pat vb),
                             patRegion=(#patRegion vb)}
			        		)
			        	in
			        		Dec.Val {rvbs=rvbs', vbs=vbs', nonexhaustiveExnMatch=nonexhaustiveExnMatch, 
			        		nonexhaustiveMatch=nonexhaustiveMatch, tyvars=tyvars}
			        	end)
	    		and loop flag boundedvars functionpat e =
		       		case (Exp.node e) of
		          		Exp.App (e1, e2) => Exp.make (Exp.App (loop flag boundedvars functionpat e1, loop flag boundedvars functionpat e2), Exp.ty e)
		        		| Exp.Case {rules, test, kind, lay, nest, noMatch, nonexhaustiveExnMatch, nonexhaustiveMatch, redundantMatch, region} =>
		        			if (Type.isBool (Exp.ty test)) then
		        				(let val test' = loop false boundedvars functionpat test
		        				     val rules' = Vector.map (rules, fn {exp, lay, pat} => 
		        				     				{exp=loop false boundedvars functionpat exp, lay=lay, pat=pat})
		        				     val e' = 
		        				     	Exp.Case {rules=rules', test=test', kind=kind, lay=lay, nest=nest, noMatch=noMatch, 
		        				     	nonexhaustiveExnMatch=nonexhaustiveExnMatch, nonexhaustiveMatch=nonexhaustiveMatch, 
		        				     	redundantMatch=redundantMatch, region=region}
		        				 in
		        				 	 Exp.make (e', Exp.ty e)
		        				 end
		        				)
		        			else
			             		(let val test' = loop true boundedvars functionpat test 
			             		     val _ = Vector.foreach (rules, fn rule =>
				             			let val p = #pat rule
				             			in	
				             				Pat.foreachVar (p, fn v => (HashTable.insert boundedvars (v, ()); HashTable.insert totalvars (v, (dummy_fr, 0))))
				             			end)
			             		     val rules' = Vector.map (rules, fn {exp, lay, pat} 
			             		     				=> {exp=loop false boundedvars functionpat exp, lay=lay, pat=pat})
			             		 	 val e' = 
			             		 	 	Exp.Case {rules=rules', test=test', kind=kind, lay=lay, nest=nest, noMatch=noMatch, 
			             		 	 	nonexhaustiveExnMatch=nonexhaustiveExnMatch, nonexhaustiveMatch=nonexhaustiveMatch, 
			             		 	 	redundantMatch=redundantMatch, region=region}
			             		 in
			             		 	 Exp.make (e', Exp.ty e)
			             		 end
			             		)
				        | Exp.Con _ => e
				        | Exp.Const _ => e
				        | Exp.Lambda l => Exp.make (Exp.Lambda (loopLambda flag boundedvars functionpat l), Exp.ty e)
				        | Exp.Let (ds, e) =>
				             (let val ds' = Vector.map (ds, loopDec flag boundedvars functionpat)
				                  val e' = loop flag boundedvars functionpat e
				                  val e'' = Exp.Let (ds', e')
				              in Exp.make (e'', Exp.ty e) end
				             )
				        | Exp.List es => Exp.make (Exp.List (Vector.map (es, loop flag boundedvars functionpat)), Exp.ty e)
				        | Exp.Record r => Exp.make (Exp.Record (Record.map (r, loop flag boundedvars functionpat)), Exp.ty e)
				        | Exp.Seq es => Exp.make (Exp.Seq (Vector.map (es, loop flag boundedvars functionpat)), Exp.ty e)
				        | Exp.Var (x, ty) => (
				        				if flag then (
				        						HashTable.insert boundedvars (x (), ()); HashTable.insert totalvars (x (), (dummy_fr, 0)); e
				        					)
				        				else if HashTable.inDomain boundedvars (x ()) then (* a use of the var locally defined in function *)
				        					((*print ("1dealing with " ^ (Var.toString (x ())) ^ "\n");*)
				        					let val ety = Exp.ty e
				        					in
				        						if (Type.isArrow ety) then
				        							let 
				        								(*val _ = print ("totalvars has " ^ (List.fold (HashTable.listItemsi totalvars, "", fn ((a,b), str)=>
				        									str ^ " " ^ (Var.toString a) 
				        								)) ^ "\n")
				        								val _ = print ("boundedvars has " ^ (List.fold (HashTable.listItemsi boundedvars, "", fn ((a,b), str)=>
				        									str ^ " " ^ (Var.toString a) 
				        								)) ^ "\n")
				        								val _ = print ("In domain? " ^ (Bool.toString (HashTable.inDomain boundedvars (x ()))) ^ " " ^
				        												"In total? " ^ (Bool.toString (HashTable.inDomain totalvars (x ()))))*)
				        								val (_, version) = HashTable.lookup totalvars (x ())
				        								val _ = HashTable.insert totalvars (x (), (dummy_fr, version+1))
				        								val myvar = Var.fromString (Var.toString (x ()))
				        								val _ = Var.setVersion myvar (version+1)
				        								val _ = HashTable.insert totalvars (myvar, (dummy_fr, 0))
				        							in Exp.var (myvar, ety) end
				        						else e
				        					end)
				        				else if (Lightenv.mem (x()) fenv) then (* a use of the the var from top level in function *)
				        					((*print ("2dealing with " ^ (Var.toString (x ())) ^ "\n");*)
				        					let val arithops = ["+", "-", "*", "/", ">", "<", ">=", "<=", "=_0",
				        										"<>_0", "sub_0", "array_0", "fromList_0", "update_0", "copy_0", "tabulate_0", "appi_0", "foldl_0", "app_0",
				        										"length_0", "size", "sub_1", "div", "lsl", "lsr", "land", "lor", "lxor", "lnot", "mod", "!_0", ":=_0",
				        										"array_1", "update_1", "nRows_0", "nCols_0", "real", "sin", "cos", "ignore_0", "make_str"] 
				        						val ety = Exp.ty e
				        						val funname = Var.toString (x ())
				        					in
				        						if (Type.isArrow ety) then
				        							if (List.exists (arithops, fn arithop => (String.compare (arithop, funname) = EQUAL))) then e
				        							else
				        								let val (_, version) = HashTable.lookup totalvars (x ())
				        									val _ = HashTable.insert totalvars (x (), (dummy_fr, version+1))
				        									val myvar = Var.fromString (Var.toString (x ()))
				        									val _ = Var.setVersion myvar (version+1)
				        									val _ = HashTable.insert totalvars (myvar, (dummy_fr, 0))
				        								in Exp.var (myvar, ety) end
				        						else e
				        					end) 
				        				else if (String.compare ((Var.toString (x())), "assert") = EQUAL
				        							orelse String.compare ((Var.toString (x())), "assertfalse") = EQUAL) then (* assert calls *)
				        					((*print ("3dealing with " ^ (Var.toString (x ())) ^ "\n");*)
				        					let val _ = if (not (HashTable.inDomain totalvars (x ()))) then 
				        								HashTable.insert totalvars (x (), (dummy_fr, 0)) else ()
				        						val ety = Exp.ty e
				        						val (_, version) = HashTable.lookup totalvars (x ())
				        						val _ = HashTable.insert totalvars (x (), (dummy_fr, version+1))
				        						val myvar = Var.fromString (Var.toString (x ()))
				        						val _ = Var.setVersion myvar (version+1)
				        						val _ = HashTable.insert totalvars (myvar, (dummy_fr, 0))
				        					in Exp.var (myvar, ety) end)
				        				else if (String.hasPrefix ((Var.toString (x())), {prefix = "arg"})) then e
				        				else if (String.compare ((Var.toString (x())), "&&") = EQUAL) then e
				        				else if (String.compare ((Var.toString (x())), "||") = EQUAL) then e
				        				else if (String.compare ((Var.toString (x())), "not") = EQUAL) then e
				        				else (* a use of closure var in function *)
				        					((*print ("Looking up for var " ^ (Var.toString (x())) ^ " with type " 
				        						^ (CoreML.visitType (Exp.ty e)));*)
				        					let val ety = Exp.ty e
				        					in
				        						if (Type.isArrow ety) then
				        							let val (_, version) = HashTable.lookup totalvars (x ())
				        								val _ = HashTable.insert totalvars (x (), (dummy_fr, version+1))
				        								val _ = HashTable.insert freevars (x (), dummy_fr)
				        								val myvar = Var.fromString (Var.toString (x ()))
				        								val _ = Var.setVersion myvar (version+1)
				        								val _ = HashTable.insert totalvars (myvar, (dummy_fr, 0))
				        								val _ = HashTable.insert freevars (myvar, dummy_fr)
				        							in Exp.var (myvar, ety)  end
				        						else (HashTable.insert freevars (x (), dummy_fr); e)
				        					end)
				        				)
				        | _ => (print ("Error: unspported experession " ^ (visitExp e)); assertfalse ())
			    and loopLambda flag boundedvars functionpat l = 
			    	let val rl = Lambda.dest l
			    		val body = #body rl
			    		val body' = loop flag boundedvars functionpat body
			    	in Lambda.make ({arg= (#arg rl), argType= (#argType rl), body=body', mayInline= (#mayInline rl)}) end
			 in	 
				(List.map (decs, loopDec true boundedvars (Var.fromString "dummymain")), freevars, totalvars)
			    (*((fn (a, b) => a) HashTable.listItemsi freevars)*)
			 end
	
	
		(*
		 * Collecting the refinements to frame relationship
		 * @param var_frame is hashtable of var to frame relation
		 * @param frame_vars is hashtable of frame to vars relation
		 *)
		fun framevars var_frame frame_vars fr = 
			let fun framevars'' pat f = 
					let val varfrs = Frame.bind pat f
					in List.foreach (varfrs, fn (var, frame) =>
				  			case frame of 
				  				  Frame.Fconstr (_, _, (subs, Frame.Qvar (k, _))) => (
				  				  	HashTable.insert var_frame (k, fr);
				  				  	if HashTable.inDomain frame_vars fr then
				  				  		let val ks = HashTable.lookup frame_vars fr
				  				  			val ks' = List.append (ks, [k])
				  				  		in 
				  				  			HashTable.insert frame_vars (fr, ks')
				  				  		end
				  				  	else 
				  				  		HashTable.insert frame_vars (fr, [k])
				  				  	)
				  				| Frame.Farrow _ => 
				  					let val k' = Frame.getFrowRefVar frame
				  					in
				  						List.foreach (k', fn k => HashTable.insert var_frame (k, fr));
				  						if HashTable.inDomain frame_vars fr then
				  							let val ks = HashTable.lookup frame_vars fr
				  								val ks' = List.append (ks, k')
				  							in HashTable.insert frame_vars (fr, ks') end
				  						else HashTable.insert frame_vars (fr, k')
				  					end
				  				| Frame.Fvar (a, (subs, Frame.Qvar (k, _))) => 
				  					(HashTable.insert var_frame (k, fr);
				  					if HashTable.inDomain frame_vars fr then 
				  						let val ks = HashTable.lookup frame_vars fr
				  							val ks' = List.append (ks, [k])
				  						in HashTable.insert frame_vars (fr, ks') end
				  					else HashTable.insert frame_vars (fr, [k]))
				  				| Frame.Frecord ([], (_, Frame.Qvar (k, _))) => (* means unit type *) (
				  					HashTable.insert var_frame (k, fr);
				  				  	if HashTable.inDomain frame_vars fr then
				  				  		let val ks = HashTable.lookup frame_vars fr
				  				  			val ks' = List.append (ks, [k])
				  				  		in 
				  				  			HashTable.insert frame_vars (fr, ks')
				  				  		end
				  				  	else 
				  				  		HashTable.insert frame_vars (fr, [k])
				  					)
				  				| _ => (print ("Unkown function parameter or incomplete record" ^ (Frame.pprint frame)); assertfalse ())
				  		) 
				  	end
				fun framevars' f = 
					case f of 
				 		  Frame.Farrow (SOME ppat, f1, f2) => 
				 			let val _ = framevars'' ppat f1
				 			in
				 				case f2 of 
				 					  Frame.Farrow _ => framevars' f2
				 					| _ => ()
							end  
						| Frame.Farrow (_, f1, f2) => ()	
						| _ => (print "Omiting the top level bindings for framevars relationship" ;())
			in
				framevars' fr
			end
	    
		(* 
		 * @param cs is the labeled_constrained list for all the frame_constrated enclosed into it
		 * @param binding_table is the (pat, exp) hash_table for binding definition
		 * @param call_deps is the (pat, pat) hash_table for call chain
		 * @param binding_frame is the (pat, frame) hash_table for binding frame definition
		 * @param freevars is the free variables
		 *)
		fun check cs binding_table call_deps binding_frame paths insidefunbindings fenv decs freevars totalvars polymatching_table invariants = 
			let 
				val _ = print "Verifying the program ...\n"
				val _ = (result := false)
				val postcondition_ks = HashTable.mkTable (hash_fn o (Var.toString), Var.logic_equals) (37, Not_found)
				val sbi = make_binding_index cs binding_table call_deps binding_frame insidefunbindings postcondition_ks fenv
				val _ = print "make work list of bindings ...\n"
				val w = make_initial_worklist sbi
				(* Initially, all the functions is abstracted into true arrow true as a start *)
				val _ = print "Generating the first abstraction ...\n"
				val s = make_initial_solution sbi binding_frame binding_table postcondition_ks invariants (* Initial abstraction with the invariant given *)
				
				
				
				val hov = HashTable.mkTable (hash_fn o (Var.toString), Var.logic_equals) (17, Common.Not_found)
				
				val _ = List.foreach (HashTable.listItemsi binding_frame, fn (funpat, funframe) =>
					let val curfunvar = Constraintgen.pat_var funpat
						
						(*val funvar_env = Frame.arrowframe_parameter_refinement_vars (Lightenv.find curfunvar fenv)*)
						fun analyzeFunFrame'' pat fr = 
						let val varfrs = Frame.bind pat fr
						in List.foreach (varfrs, fn (var, frame) =>
					  			case frame of 
					  				  Frame.Farrow _ =>
										let val _ = print ("\n=========" ^ (Var.toString var) ^ "=========\n")
											val k = Frame.getFrowRefVar fr
											val _ = print "\nNote tool has not supported higher order function with a record return value\n"
											val _ = assert ((List.length k) = 1)
											val k = List.first k (* Not appropirate for record return value *)
											val valu = Var.mk_ident ("V")
											val name = Var.mk_ident ("")
											val paramvars = (*Frame.hofunFramevars frame (var)*) Frame.hofunFramevars_in_version frame
											val pred = Predicate.Atom (
												Predicate.PVar valu, Predicate.Eq, Predicate.FunApp ("P" ^ (Int.toString (List.length paramvars)), (Predicate.PVar var) :: paramvars))
											(*val pred = 
												if (recflag) then pred
												else Predicate.big_and (pred :: (Frame.hofunFramevars_in_version_2 var frame))*)
											
											(*val pred = Predic
											ate.Or (Predicate.Not (Frame.funframe_pred var frame), pred)*)
											val q = (name, valu, pred)
											val kqs = if (HashTable.inDomain s k) then HashTable.lookup s k else []
											val id = HashTable.lookup (#pats sbi) funpat
											val sri = #sri (HashTable.lookup (#orig sbi) id)
											val ks = Constraint.getCurriedKs sri k
											val _ = print ("\nthe curried ks from " ^ (Var.toString k) ^ " is listed below: \n")
											val _ = List.foreach (ks, fn k => print ((Var.toString k) ^ " "))
											val _ = print ("\nthe post ks is listed below: \n")
											val _ = List.foreach (HashTable.listItemsi postcondition_ks, fn (k,_) => print ((Var.toString k) ^ " "))
										in 
											HashTable.insert s (k, [q]);
											HashTable.insert hov (k, ());
											List.foreach (ks, fn k => (
												if (HashTable.inDomain postcondition_ks k) then (* is a postcondition k *) (
													print ("\n" ^ (Var.toString k) ^ " post\n"); ()
												) (* Don't add higher order value for functional postcondition *)
												else (* is not a postcondition k *) (
													print ("\n" ^ (Var.toString k)^ " pre\n"); 
													HashTable.insert s (k, kqs @ [q]);
													HashTable.insert hov (k, ())
												) (* higher order value must be added in the last *)
											))
										end
									| _ => ()
					  		) 
					  	end
						fun analyzeFunFrame' fr = 
							case fr of 
						 		  Frame.Farrow (SOME ppat, f1, f2) => 
						 			let val _ = analyzeFunFrame'' ppat f1
						 			in
						 				case f2 of 
						 					Frame.Farrow _ => analyzeFunFrame' f2
						 					| _ => ()
									end  
								| Frame.Farrow (_, f1, f2) => ()	
								| _ => ()
					in
						analyzeFunFrame' funframe
					end
				)
			
				val back_s = HashTable.copy s
			
				val _ = print "\nFinal snapshot of initial abstraction\n"
				
				
				val _ = List.foreach (HashTable.listItemsi binding_frame, fn (a, b) => print (
			  		 (Var.toString (Constraintgen.pat_var a)) ^ " : " ^
			  		 (Frame.pprint_final b (Constraint.solution_map s)) ^ "\n")
			  		 )
				
				(* Find the frame <--> refinements relations *)
				val var_frame = HashTable.mkTable (hash_fn o (Var.toString), Var.logic_equals) (13, Not_found)
				val frame_vars = HashTable.mkTable (hash_fn o (Frame.pprint), Frame.same_shape false) (13, Not_found)
				
				(*val _ = List.foreach (HashTable.listItemsi binding_frame, fn (p, f) => framevars var_frame frame_vars f)*)
				
				(* Record in non_convergence_table the location where the program verificaton cannot converge *)
				val non_convergence_table = ref []                      
				val force_convergence_table = HashTable.mkTable (hash_fn o (Int.toString), (op=)) (17, Not_found)                          
				val parameterIndex_table = HashTable.mkTable (hash_fn o (Var.toString), Var.logic_equals) (37, Not_found)
				val postcon_non_cvg_table = HashTable.mkTable (hash_fn o (fn (pat, cid) => (Var.toString (pat_var pat) ^ (Int.toString cid))), 
						fn ((pat1, cid1), (pat2, cid2)) => (pat_eq (pat1, pat2) andalso (cid1 = cid2))) (11, Not_found)
				val _ = print "\nBegin fixpoint computation\n"
				val result = iterate_verify sbi s back_s w binding_frame paths fenv decs freevars totalvars call_deps 
						var_frame frame_vars hov force_convergence_table non_convergence_table polymatching_table parameterIndex_table postcon_non_cvg_table				
			in
				print ("Verification completes. Result is " ^ (Bool.toString result) ^ "\n");
				if (List.length (!non_convergence_table) > 0) then
					List.foreach ((!non_convergence_table), fn (pat, expstr) => print ("Not converge when verifying constraint from function " ^  
																			(Var.toString (Constraintgen.pat_var pat)) ^ " and the expression " ^ expstr ^ "\n"))	
				else print "\nCheck convergence step 1 passes.\n";
				
				if ((HashTable.numItems postcon_non_cvg_table) > 0) then
					List.foreach (HashTable.listItemsi postcon_non_cvg_table, fn ((pat, cid), ci) => (
						print ("\nprocedure " ^ (Var.toString (pat_var pat)) ^ " with constriant id " ^ (Int.toString cid) ^ " has " ^ 
							(Int.toString ci) ^ " times of postcondition or higher order function propagation\n");
				
						if (ci >= 10) then
							print ("Not convergence when verifing constraint from function " ^ (Var.toString (Constraintgen.pat_var pat)) ^ "\n")
						else ())
					)
				else print "\nCheck convergence step 2 passes.\n";
				
				s
			end
			
			
			
		(*
		 * @type qualify_implementation: Lightenv.t -> Lightenv.t -> Dec.t list -> unit
		 * @param fenv is the global env with built-in frames
		 * @param ifenv is the env with frame of program constructs provided by third party
		 * @param str is the Dec.t list obtained from MLton CoreML
		 * @param ofops is the outfile operation for test file 
		 * @return a tuple of
		 *		cs is the labeled_constrained list for all the frame_constrated enclosed into it
		 * 		binding_table is the (pat, exp) hash_table for binding definition
		 * 		call_deps is the (pat, pat) hash_table for call chain
		 * 		binding_frame is the (pat, frame) hash_table for binding frame definition
		 *)
		open Constraint
		
		fun qualify_implementation fenv ifenv renv str inv_file =
			let (* Loading the invariants necessary *)
				val invariants = case inv_file of
	      		  	SOME inv_file => (
	      		  		print ("\n Now loading qualifier file " ^ inv_file ^ "\n");
	      		  		let val inv = IParser.parse (inv_file)
	      		  		in Invariant.parse inv end
	      		  	)
	      			| NONE => []
	      			
	      		val _ = print (List.fold (invariants, "\nInvariants includes ", fn ((vi, vf, ip), str) => 
	      			(str ^ (Var.toString vi) ^ " " ^ (Var.toString vf) ^ " " ^ (Predicate.pprint ip) ^ ", ")
	      		))	
				
				(* Build the global environment and constraints between frames *)
				(*val _ = print ("the given env is " ^ Constraint.pprint_pure_env fenv)*)
				(* Have to collect all the functions is the initial env, we do not want to verify them *)
				val builtinfuns = Lightenv.domain fenv
				
				
				(* Find all the free variables in the program which must read value from the closure *)
				(*val _ = print "Collecting the variable that could be closure related\n"*)
				val (str, freevars, totalvars') = closurevars str fenv
				val _ = print "Collected\n"
				val totalvars = HashTable.mkTable (MLton.hash, Var.pointer_equals) (HashTable.numItems totalvars', Common.Not_found)
				val _ = List.foreach (HashTable.listItemsi totalvars', fn (a, (b, c)) => HashTable.insert totalvars (a, b))
				
				
				val polymatching_table = HashTable.mkTable (hash_fn o (Var.toString), Var.logic_equals) (117, Not_found)
				
				(* in the toplevel and dummy main; after executing it, side effect is freevars is stuffed with frames *)
				val (fenv, renv, cs, rcs) = RelConstraintgen.constrain_structure fenv renv [] str polymatching_table
				(*val (fenv, cs, binding_table, call_deps, binding_frame, paths, insidefunbindings) = Constraintgen.constrain_structure 
						fenv 
						[] 
						str 
						true  
						(Pat.var (Var.fromString "dummymain", Type.var(Tyvar.newNoname {equality = false})))
						freevars
						totalvars
						polymatching_table*)
        val binding_table = HashTable.mkTable (hash_fn o (Var.toString) o pat_var, pat_eq) 
                              (17, Not_found)
        val binding_frame = HashTable.mkTable (hash_fn o (Var.toString) o pat_var, pat_eq) 
                              (17, Not_found)
        val call_deps = ref []
        val paths = ref []
        val insidefunbindings = HashTable.mkTable (hash_fn o (Var.toString) o pat_var, pat_eq) (17, Not_found)

				(* Constraints with additional frames given by user or third party tools *)
				(* val cs = (List.map ((Le.maplistfilter (mfm fenv) ifenv), (lbl_dummy_cstr))) @ cs *)
				val _ = print ("\nThe inferred constraints with a total number of " ^ (Int.toString (List.length cs)) ^ " are shown below \n")
				val _ = List.foreachi (cs, (fn (i,c) => 
						(print (Int.toString i); print ": "; print (Constraint.pprint (case c of Cs.lc c' => #lc_cstr c')); print "\n")))
				val _ = print ("the final env is " ^ Constraint.pprint_pure_env fenv)
        val _ = print "**********************************************************\n"
        val _ = print ("The inferred Relation Constraints with a total number of " ^ (Int.toString (List.length rcs)) ^ " are shown below \n")
				val _ = List.foreachi (rcs, (fn (i,c) => 
						(print (Int.toString i); print ": "; print (RCs.pprint (case c of RCs.lc c' => #lc_cstr c')); print "\n")))
				val _ = print ("the final env is " ^ RCs.pprint_pure_renv renv)
				(* Filter out all the builtin in fun calls *)
				val cdeps = List.removeAll ((!call_deps), fn (pat1, pat2) => 
					(List.exists (builtinfuns, fn f => Var.logic_equals (Constraintgen.pat_var pat2, f))) orelse
					String.equals ((Var.toString (Constraintgen.pat_var pat2)), "assert")
				)
				val paths = (!paths);
				(*val _ = List.fold (paths, (), fn ((bpat, path, pred, assertflag), _) => 
			    			print ((Var.toString (Constraintgen.pat_var bpat)) ^ (Predicate.compact_pprint_pexpr path) ^ " " ^ (Predicate.pprint pred) ^ " " ^
			    		(Bool.toString assertflag) ^ "\n"))*)
				val s = check cs 
                      binding_table 
                      cdeps 
                      binding_frame 
                      paths 
                      insidefunbindings 
                      fenv 
                      str 
                      freevars 
                      totalvars 
                      polymatching_table 
                      invariants
		  		
		  		val (nb_refinements, max_pred_len) = 
		  			List.fold (HashTable.listItems binding_frame, (0, 0), fn (fr, (nb_refinements, max_refinement_len)) =>
		  				let val ks = case fr of 
		  					Frame.Farrow _ => Frame.arrowframe_refinement_vars fr
		  					| _ => Frame.refinement_vars fr
		  				in
		  					List.fold (ks, (nb_refinements, max_refinement_len), fn (k, (nb_refinements, max_refinement_len)) =>
		  						if (HashTable.inDomain s k) then
		  							List.fold (HashTable.lookup s k, (nb_refinements, max_refinement_len), fn ((_, _, p), (n_r, m_l)) =>
										let val plen = Predicate.size p
										in
											if (plen > m_l) then (n_r + 1, plen) 
											else (n_r + 1, m_l) 
										end
									)  
		  						else (nb_refinements, max_refinement_len)
		  					)
		  				end
		  			)			
		  		
		  		(*val allfuns = HashTable.listItems binding_frame
		  		val calls = HashTable.listItems call_deps
		  		val uncalls = Common.map_partial (fn f => 
		  			not (List.exists (calls, fn c => (Var.logic_equals (Constraintgen.pat_var f, Constaintgen.pat_var c))))
		  		) allfuns
		  		*)
		  		val _ = print "\n\nThe final depenedent types for functions inferred are listed below:  \n\n"
		  	in
          ()
		  		(*List.foreach (HashTable.listItemsi binding_frame, fn (a, b) => print (
		  		 (Var.toString (Constraintgen.pat_var a)) ^ " : " ^
		  		 (Frame.pprint_final b (Constraint.solution_map s)) ^ "\n--------------------------------------------------\n")
		  		 );
	
		  		print ("The number of refinement we generated is " ^ (Int.toString nb_refinements) ^ "\n");
				print ("The maximum length of refinement we generate is of size " ^ (Int.toString max_pred_len) ^ "\n");
				print ("Verification stats are given below \n");
				VerificationCondition.print_stats ();
				print ("During verification, stats of intermediate refinements are given below \n");
				print ("The number of intermediate refinements generated is " ^ (Int.toString (! (VerificationCondition.intermediate_nb_refinement))) ^ "\n"
						^ "The maximum length of intermediate refinements generated is " ^ (Int.toString (! (VerificationCondition.intermediate_max_refinement_len))) ^ "\n");
				VerificationCondition.reset ();
				print ("The theorem prover stats is given below: ");
				TheoremProver.print_stats ()*)
		  	end
	end
