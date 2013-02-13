

structure Constraint = 
	struct
		open Atoms
		open CoreML

		structure F = Frame
		structure Le = Lightenv
		structure P = Predicate
		structure TP = TheoremProver
		structure B = Builtin
		
		structure C = Common
		structure Cf = Control
	
		open HashTable
		open Common
		open Pattern
		
		(**************************************************************)
		(**************** Type definitions: Constraints ***************) 
		(**************************************************************)
		
		type fc_id = int option 
		type subref_id = int 	                         
		
		type guard_t = (Var.t * int * bool) list
		
		datatype frame_constraint =
        (* Gamma;guard |-  F.t => F.t*)
		    SubFrame of Le.t * guard_t * F.t * F.t
		  | WFFrame of Le.t * F.t
		
		datatype labeled_constraint = lc of {
		  lc_cstr: frame_constraint,
		  lc_orig: origin,
		  lc_id: fc_id,
		  lc_binding : Pat.t
		}
		and origin =
		    Loc of (Exp.t option)
		  | Assert of Exp.t 
		  | Cstr of labeled_constraint
	
		
		(* In our solving procedure, we indeed use refinement_constraints 
		 * Thus every refinement constraint comes from frame_constraints; attached with subref_id
		 * bool value is used as functional subtyping indicator
		 *)
		datatype refinement_constraint =
		    SubRef of Le.t * guard_t * F.refinement * F.refinement * bool * int * (Con.t option) * int * (subref_id option) 
		  | WFRef of Le.t * F.refinement * (subref_id option) 
		  
		val hash_fn = HashString.hashString
		
		(**************************************************************)
		(********************** Misc. Constants ***********************)
		(**************************************************************)
	
		(* return a new constraint indexing *)
		fun fresh_fc_id () = 
		  let val r = ref 0 
		  in fn () => incr r; SOME (!r) end
		
		(* Unique variable to qualify when testing sat, applicability of qualifiers...
		 * this is passed into the solver *) 
		val qual_test_var = Var.fromString ("AA")
		val qual_test_expr = P.PVar qual_test_var
		
		(* If there is no pending substitution then return true *)
		fun is_simple_constraint refcons = 
			case refcons of
				  SubRef (_, _, ([],F.Qvar _), ([], F.Qvar _), _, _, _, _, _) => true 
				| _ => false
		
		fun is_subref_constraint refcons =  
			case refcons of
				  SubRef _ => true 
				| _ => false
		
		fun is_wfref_constraint refcons = 
			case refcons of
				  WFRef _ => true 
				| _ => false
		
		(* Try to find the solutions for a refinement; Sol is a hashtable *)
		fun solution_map s k = 
			(HashTable.lookup s) k handle Not_found => ((*print ("ERROR: solution_map couldn't find: " ^ (Var.toString k)); *)assertfalse())
		
		(**************************************************************)
		(**************************** Stats ***************************)
		(**************************************************************)
		val stat_wf_refines = ref 0
		val stat_sub_refines = ref 0
		val stat_simple_refines = ref 0
		val stat_refines = ref 0
		val stat_imp_queries = ref 0
		val stat_valid_imp_queries = ref 0
		val stat_matches = ref 0 
		
		fun pprint refcons = (
			case refcons of 
		    	  SubFrame (env,g,f1,f2) =>
		    	  	(* "env is " ^ (pprint_env_pred NONE env) ^ " guard is " ^ (P.pprint(guard_predicate () g)) 
		    	  		^ *) "subframe ls: " ^ (F.pprint f1) ^ " rs: " ^ (F.pprint f2)
		  		| WFFrame (env,f) =>
		  			(* "env is " ^ (pprint_env_pred NONE env) ^ *)
		  				"wellformed frame: " ^ (F.pprint f))
		
		fun pprint_io io = 
			case io of
		    	  SOME id => "(" ^ (Int.toString id) ^ ")"
		  		| NONE    => "()"
		
		fun pprint_ref so refcons =
			case refcons of 
		    	  SubRef (env,g,r1,r2,_,_,_,_,io) =>
		    		"SubRef" ^ (pprint_io io) (* ^ ((pprint_env_pred so) env) ^ (P.pprint (guard_predicate () g))*) ^
		    		" r1 is " ^ (F.pprint_refinement r1) ^ " r2 is " ^ (F.pprint_refinement r2) ^ "\n"
		  		| WFRef (env,r,io) =>
		  			"WFRef" ^ (pprint_io io) (*^ ((pprint_env_pred so) env)*) ^ (F.pprint_refinement r) ^ "\n"
		
		(**************************************************************)
		(************* Constraint Simplification & Splitting **********) 
		(**************************************************************)
		
		(* gm is the map; x is the key; light env maps var to frames 
		fun simplify_frame gm x f = 
			if not (HashTable.inDomain gm x) then f 
			else
			    let val pos = HashTable.lookup gm x 
			    in
				    case f of 
					      F.Fconstr (a, b, (subs,F.Qconst[(v1,v2,P.Iff (v3,p))])) =>
							if Predicate.logic_equals_pexp v3 (B.tag (P.PVar v2)) then 
						        let val p' = if pos then p else P.Not p 
						        in F.Fconstr (a, b, (subs,F.Qconst[(v1,v2,p')])) end
					        else f
					    | F.Frecord (a, (subs,F.Qconst[(v1,v2,P.Iff (v3,p))])) =>
					    	if Predicate.logic_equals_pexp v3 (B.tag (P.PVar v2)) then
						        let val p' = if pos then p else P.Not p
						        in F.Frecord (a, (subs,F.Qconst[(v1,v2,p')])) end
					        else f
					    | _ => f
			    end
		
		fun simplify_env env g =
			let 
				val guard_table = HashTable.mkTable (hash_fn o (Var.toString), Var.logic_equals) (37, Not_found)
				val gm = List.fold (g, guard_table, (fn ((x, b, _), m) => (HashTable.insert m (x, b) ; m))) 
			in
			  	Le.fold 
			    (fn x => fn f => fn env' =>
			      case f of 
			      	  F.Fconstr _ => Le.add x (simplify_frame gm x f) env' 
			      	| F.Frecord _ => Le.add x (simplify_frame gm x f) env'
			      	| _ => env') env (Le.empty 37)
			end
		
		fun simplify_fc c = case c of 
			  lc c' => (case (#lc_cstr c') of
		  		  WFFrame _ => c 
		  		| SubFrame (env, g, a, b) =>
			    	let val env' = simplify_env env g 
			    	in
				      	(* let _ = printf "@[Simplify env to: %a@.@]" (pprint_env_pred None) env' in *)
				      	lc {lc_cstr = SubFrame(env', g, a, b),
		  				 lc_orig = #lc_orig c',
		  				 lc_id = #lc_id c',
		  				 lc_binding = #lc_binding c'}
				    end)
		*)		    		
		(* Make labeled constraint 
		 * c is a labeled constraint; fc is a frame constraint; 
		 *)
		fun make_lc c fc funflag recordIndex con conrecordIndex = case c of 
			  lc c' => (lc {lc_cstr = fc, lc_orig = Cstr c, lc_id = #lc_id c', lc_binding = #lc_binding c'}, funflag, recordIndex, con, conrecordIndex)
			  		
		fun lequate_cs env g c funflag recordIndex con conrecordIndex variance (f1, f2) = 
			case variance of
		  		  F.Invariant => [make_lc c (SubFrame(env,g,f1,f2)) funflag recordIndex con conrecordIndex, 
		  		  					make_lc c (SubFrame(env,g,f2,f1)) funflag recordIndex con conrecordIndex]
		  		| F.Covariant => [make_lc c (SubFrame(env,g,f1,f2)) funflag recordIndex con conrecordIndex]
		  		| F.Contravariant => [make_lc c (SubFrame(env,g,f2,f1)) funflag recordIndex con conrecordIndex]
		
		fun match_and_extend env (l1,f1) (l2,f2) =
			case (l1,l2) of
		  		  (SOME p, NONE) => Le.env_bind env p f2
		  		| (NONE, SOME p) => Le.env_bind env p f2
		  		| (SOME p1, SOME p2) =>
		  			if Pattern.same (p1, p2) then Le.env_bind env p1 f2 else env
		  		| _  => env
						
		(* The final returned results would be pairs of (original labled constriant and refinement constraint)*)
		fun split_sub fr funflag recordIndex con conrecordIndex = 
			case fr of
				  lc {lc_cstr = WFFrame _, ...} => assertfalse () 
				| c as (lc {lc_cstr = SubFrame (env,g,f1,f2), ...}) =>
					  case (f1, f2) of
						  	(F.Farrow (l1, f1, f1'), F.Farrow (l2, f2, f2')) => 
						      let val env' = match_and_extend env (l1,f1) (l2,f2) 
						      in
						      	((lequate_cs env g c true recordIndex con conrecordIndex F.Covariant (f2, f1)) @ 
						      	 (lequate_cs env g c true recordIndex con conrecordIndex F.Covariant (f1', f2')), [])
						      end
						  | (F.Fvar (_, r1), F.Fvar (_, r2)) => ([], [(Cstr c, SubRef (env,g,r1,r2,funflag,recordIndex,con,conrecordIndex,NONE))])
						  | (F.Funknown, F.Funknown) => ([],[]) 
						  | (F.Fconstr (p1, f1s, r1), F.Fconstr(p2, f2s, r2)) => (
						  	  (*print ("\nCurrent con is " ^ (case con of SOME con => (Con.toString con) | NONE => "none con") ^ "\n");*)
						      (C.flap2i 
						      	(fn i => fn f1' => fn f2' => (
						      		lequate_cs env g c funflag (i+1) con conrecordIndex F.Covariant (f1', f2') (* Still get labeled constraints *)
						      		)
						      	)
						      	f1s f2s,
						      	[(Cstr c, SubRef(env,g,r1,r2,funflag,recordIndex,con,conrecordIndex,NONE))]) 
						      	(* pair of original labeled constraint and refinement constraint*)
						    )
						  | (F.Frecord ([], (_, F.Qvar (k, _))), F.Fvar (_, r2)) => ([], []) (* unit type *)
						  | (F.Fvar (_, r1), F.Frecord ([], (_, F.Qvar (k, _)))) => ([], []) (* unit type *)
						  | (F.Frecord (fld1s, r1), F.Frecord (fld2s, r2)) => (
						      (C.flap2i 
						         (fn i => fn (f1',_) => fn (f2',_) => (
						         	lequate_cs env g c funflag (i+1) con conrecordIndex F.Covariant (f1', f2')
						         	)
						         )
						         fld1s fld2s, 
						         [(Cstr c, SubRef (env,g,r1,r2,funflag,recordIndex,con,conrecordIndex,NONE))])
						    )
						       (*
						       Mutable feature is not supported in current version
						       if List.exists (fun (_, _,m) -> m = Asttypes.Mutable) fld1s
						       then [(Cstr c, SubRef (env,g,r1,r2,None)); (Cstr c, SubRef (env,g,r2,r1,None))]
						       else [(Cstr c, SubRef (env,g,r1,r2,None))])
						       *)
						  | (F.Fvar (_, r1), F.Fconstr (_, _, r2)) => ([], [(Cstr c, SubRef(env,g,r1,r2,funflag,recordIndex,con,conrecordIndex,NONE))]) 
						  | (F.Fconstr (_, _, r1), F.Fvar (_, r2)) => ([], [(Cstr c, SubRef(env,g,r1,r2,funflag,recordIndex,con,conrecordIndex,NONE))])
						  | (F.Fsum (_, f1s, r1), F.Fsum (_, f2s, r2)) => (
						  		print ("\nFsum1 " ^ (Frame.pprint f1) ^ "<: Fsum2 " ^ (Frame.pprint f2) ^ "\n");
						  		(List.fold2 (f1s, f2s, [], fn (f1, f2, l) =>
						  			case (f1, f2) of 
						  				((_, F.Fconstr (p1, f1s, r1)), (con, F.Fconstr (p2, f2s, r2))) =>
						  					let val _ = print ("\n" ^ (Con.toString con) ^ "\n")
						  						val l' = (C.flap2i 
						  							(fn i => fn f1' => fn f2' => 
						  								(lequate_cs env g c funflag recordIndex (SOME con) (i+1) F.Covariant) (f1', f2')
						  							)
						  							f1s f2s
						  						)
						      			 	in (l@l') end
						  				| _ => (print "\nSum type error\n"; assertfalse ())
						  		), [(Cstr c, SubRef(env,g,r1,r2,funflag,recordIndex,con,conrecordIndex,NONE))])
						  	)
						  | (F.Fconstr (p1, f1s, r1), F.Fsum (_, f2s, _)) =>
						  		let val f2 = List.peek (f2s, fn (c, f) => Frame.same_shape true (f1, f))
						  			val f2 = case f2 of SOME (c2, f2) => f2 | NONE => (print ("\nIll typed constructor" ^ (Frame.pprint f1) ^ "\n"); assertfalse ())
						  			val f2 = Frame.unfoldRecursiveFrame f2 p1 f2s 
						  		in case f2 of 
						  			F.Fconstr (p2, f2s, r2) =>
						  				(C.flap2 (lequate_cs env g c funflag recordIndex con conrecordIndex F.Covariant) f1s f2s,
						      			 [(Cstr c, SubRef(env,g,r1,r2,funflag,recordIndex,con,conrecordIndex,NONE))])
						  			| _ => (print "\nSum type error\n"; assertfalse ())
						  		end
						  | (F.Fsum (_, f1s, _), F.Fconstr (p2, f2s, r2)) =>
						  		let val f1 = List.peek (f1s, fn (c, f) => Frame.same_shape true (f, f2))
						  			val f1 = case f1 of SOME (c1, f1) => f1 | NONE => (print ("\nIll typed constructor" ^ (Frame.pprint f2) ^ "\n"); assertfalse ())
						  			val f1 = Frame.unfoldRecursiveFrame f1 p2 f1s
						  		in case f1 of 
						  			F.Fconstr (p1, f1s, r1) =>
						  				(C.flap2 (lequate_cs env g c funflag recordIndex con conrecordIndex F.Covariant) f1s f2s,
						      			 [(Cstr c, SubRef(env,g,r1,r2,funflag,recordIndex,con,conrecordIndex,NONE))])
						  			| _ => (print "\nSum type error\n"; assertfalse ())
						  		end
						  | (_,_) => 
						      (print ("@[Can't@ split:@ " ^ (F.pprint f1) ^ "@ <:@ " ^ (F.pprint f2) ^ "@]"); assertfalse ())
		
		fun split_wf fr = 
			case fr of
				  lc {lc_cstr = SubFrame _, ...} => assertfalse () 
				| c as (lc {lc_cstr = WFFrame (env,f), lc_binding = b, ...}) =>
					let 
						fun make_wff env f = (lc {lc_cstr = WFFrame (env, f), lc_orig = Cstr c, lc_id = NONE, lc_binding = b}, false, 0, NONE, 0) 
					in
					  	case f of
					  		  F.Fconstr (_, l, r) =>
					  			(List.map (l, (make_wff env)),
					  			[(Cstr c, WFRef (Le.add qual_test_var f env, r, NONE))])
						  	| F.Farrow (l, f, f') =>
						  		let val env' = case l of NONE => env | SOME p => Le.env_bind env p f 
						  		in ([make_wff env f, make_wff env' f'], []) end
						  	| F.Frecord (fs, r) =>
						  		(List.map (fs, (fn (f',_) => make_wff env f')),
						  		[(Cstr c, WFRef (Le.add qual_test_var f env, r, NONE))])
						  	| F.Fvar _ => ([], [])
						  	| F.Funknown => ([],[]) 
						  	| F.Fsum (_, fs, r) =>
						  		(List.map (fs, fn (c, f) => (make_wff env f)),
					  			[(Cstr c, WFRef (Le.add qual_test_var f env, r, NONE))])
					end
		
		fun split cs =
		  (assert (List.forall (cs, (fn c => case c of lc c' => NONE <> #lc_id c')));
		  C.expand 
		    (fn (c, funflag, recordIndex, con, conrecordIndex) => case c of lc c' => 
		    	(case #lc_cstr c' of 
		    	SubFrame _ => split_sub c funflag recordIndex con conrecordIndex | WFFrame _ => split_wf c)
		    	)
		    (List.map (cs, fn c => (c, false, 0, NONE, 0))) [])
		
		(**************************************************************)
		(********************* Constraint Indexing ********************) 
		(**************************************************************)
		
		structure WH = Functional(
		    struct 
		      type t = subref_id * (int * bool * fc_id) 
		      fun compare (_,(i,j,k)) (_,(i',j',k')) = 
		        if i <> i' then 
		        	if i < i' then 1 else ~1
		        else if j <> j' then 
		        	case (j, j') of
		        		  (false, true) => 1
		        		| (true, false) => ~1
		        		| _ => assertfalse ()
		        else 
		          	case (k, k') of
		          		  (NONE, NONE) => 0
		          		| (NONE, SOME _) => 1
		          		| (SOME _, NONE) => ~1
		          		| (SOME k1, SOME k2) =>
		          			if k1 < k2 then 1 else if k1 = k2 then 0 else ~1
		    end)
		
		(* SIM is declared as a map with interger key *)
		type ref_index =  
		  { orig: (subref_id, labeled_constraint) hash_table, (* id -> orig *)
		    cnst: (subref_id, refinement_constraint) hash_table,  (* id -> refinement_constraint *) 
		    rank: (subref_id, (int * bool * fc_id)) hash_table,  (* id -> dependency rank *)
		    depm: (subref_id, subref_id list) hash_table,         (* id -> successor ids *)
		    pend: (subref_id, unit) hash_table,  (* id -> is in wkl ? *)
		    rhs_km : (Var.t, subref_id list) hash_table,
			curried_k_deps : (Var.t, Var.t list) hash_table, (* kr -> kl *)		    
			app_k_deps : (Var.t, Var.t) hash_table, (* kl -> kr *) 
			postcondition_ks : (Var.t, unit) hash_table
			(*
			 * Doc:
			 * Different usage:
			 * 1. When we do functional subtyping (subtyping of function refinements), we will take care of 
			 * path information, so subtyping go forward or backward only there is no path information.
			 * In this case, we use curried_k_deps
			 * 2. When we do test generation of function parameter, we have to give the body of this function.
			 * In this case, we must know the conservative function return value.
			 * So we do not care the path information, then use app_k_deps.
			 *)
		  }
		
		(* Get refinement id *)
		fun get_ref_id refcons =
			case refcons of
				  WFRef (_,_,SOME i) => i
				| SubRef (_,_,_,_,_,_,_,_,SOME i) => i 
				| _ => assertfalse ()
		
		(* Get refinment constraint rank *)
		fun get_ref_rank {orig=orig',cnst=cnst',rank=rank',depm=depm',pend=pend',
							rhs_km=rhs_km', curried_k_deps=kdeps', app_k_deps=app_k_deps', postcondition_ks=postcondition_ks'} c = 
			HashTable.lookup rank' (get_ref_id c) handle Not_found => 
		    	(print ("ERROR: @[No@ rank@ for:@ " ^ ((pprint_ref NONE) c) ^  "@\n@]"); raise Not_found)
		
		(* Get refinement constraint *)
		fun get_ref_constraint {orig=orig',cnst=cnst',rank=rank',depm=depm',pend=pend',
							rhs_km=rhs_km', curried_k_deps=curried_k_deps', app_k_deps=app_k_deps', postcondition_ks=postcondition_ks'} i = 
			HashTable.lookup cnst' i handle Not_found =>
				(print "ERROR: get_constraint"; raise Not_found)
		
		(* Collect refinements for a refinement constrants on left part *)
		fun lhs_ks refcons =
			case refcons of
				  WFRef _  => assertfalse ()
				| SubRef (env,_,(_,qe),_,_,_,_,_,_) =>
					let val ks = Le.fold (fn _ => fn f => fn l => F.refinement_vars f @ l) env []
					in
						case qe of 
							  F.Qvar (k, _) => k::ks 
							| _ => ks
					end
		
		(* Collect refinements for a refinement constrants on right part *)
		fun rhs_k refcons = 
			case refcons of
				  SubRef (_,_,_,(_,F.Qvar (k, _)),_,_,_,_,_) => SOME k
		  		| _ => NONE
		
		(* Get the refinement chain list.
		 * In refinement constraint generation, there is a lot of simple refinement implication. 
		 * such as env+k1 => k2 or env+(v=x)=>k2 in which x is binded in env by a simple refinement k1
		 * We want to get k1->k2 chain list. So when a refinement is set, the refinements on its chain list should also be set. 
		 *)
		fun iter_get_k_deps env subs qe =
			let fun get_k_deps li = 
				case qe of 
					  Frame.Qvar (kl, _) => (kl :: li)
					| Frame.Qconst qlist => 
						List.fold (qlist, li, fn (q, li) => 
							let val p = Qualifier.apply qual_test_expr q
								val p = Predicate.apply_substs subs p
							in
								case p of 
									  (Predicate.Atom (Predicate.PVar x, Predicate.Eq, Predicate.PVar y)) =>
									  	let val tvar = 
									  		if Var.logic_equals (x, qual_test_var) then SOME y
									  		else if Var.logic_equals (y, qual_test_var) then SOME x
									  		else NONE
									  	in
									  		case tvar of 
									  			  NONE => li
									  			| SOME t => (* We only want the t to be argument *)
									  				if (String.hasPrefix ((Var.toString t), {prefix = "x_"})) then
										  				let val mf = (Le.find t env) 
										  					handle Not_found => (print "\nNOTFOUND for curried_k_deps\n"; print (Var.toString t); assertfalse())
										  				in
										  					case mf of
										  						  Frame.Fconstr (_, _, (subs, qe)) => (iter_get_k_deps env subs qe) @ li
										  						| Frame.Frecord (f_, (subs, qe)) => (iter_get_k_deps env subs qe) @ li
										  						| _ => li
										  				end
									  				else li
									  	end
									| _ => li
							end
						)
			in
				get_k_deps []
			end
		
		
		fun simplylc c = case c of lc c' => c'
		
		fun get cstr' =
	    	case #lc_orig cstr' of
		        Loc exp => (case exp of SOME exp => exp | NONE => (
		        	(*print ("\nCannot get an Expression due to Recursion.\n"); *)
		        	assertfalse ())
		        )
		      | Assert exp => exp
		      | Cstr cstr => get (simplylc cstr)
		
		fun get_postcondition_ks labled_cs postcondition_ks =
			List.foreach (labled_cs, fn labled_c =>
				(let val c' = simplylc labled_c
					val c = #lc_cstr c' 
					val _ = print ("\nIn get_postcondition_ks " ^ (pprint c) ^ "\n")
					val exp = get c'
					val _ = print ("\nConstraint generated by expr " ^ (CoreML.visitExp exp) ^ "\n");
				in
					case c of
						SubFrame (_, _, lf, rf) => (
							case (lf, rf) of
                (* Higher order sub-typing *)
								(Frame.Farrow _ , Frame.Farrow _) => (
									case (Exp.node (get c')) of
										Exp.App _ => ()
										| Exp.Record _ => ()
										| Exp.Case {rules, ...} => (
                      (* Hack alert! *)
											if ((Vector.length rules) > 1) then ()
											else (
                        (* Get the list of bound frame vars from
                           result frames of lf and rf *)
												let val lks = Frame.getFrowRefVar lf
													val rks = Frame.getFrowRefVar rf
													val ks = lks @ rks
                          (* add them to postcondition_ks *)
												in List.foreach (ks, fn k => (print ("\nAdding post k " ^ (Var.toString k) ^ "\n"); HashTable.insert postcondition_ks (k, ()))) end
											)	
										)
										| _ => ( (* other exprs: Con, Const, Var, Let, Seq *)
											let val lks = Frame.getFrowRefVar lf
												val rks = Frame.getFrowRefVar rf
												val ks = lks @ rks
											in List.foreach (ks, fn k => (print ("\nAdding post k " ^ (Var.toString k) ^ "\n"); HashTable.insert postcondition_ks (k, ()))) end
										)
								)
								| _ => () (* forall other SubFrame constaints *)
						)
						| _ => () (* for WFF constraints *)
						
				end) handle RuntimeError => (
					(*print "\nRecursion\n";*)
					case (#lc_cstr (simplylc labled_c)) of 
						SubFrame (_, _, lf, rf) => (
							case (lf, rf) of
								(Frame.Farrow _ , Frame.Farrow _) => (
									let val lks = Frame.getFrowRefVar lf
										val rks = Frame.getFrowRefVar rf
										val ks = lks @ rks
									in List.foreach (ks, fn k => HashTable.insert postcondition_ks (k, ())) end
								)
								| _ => (print "\nTOOL ERROR, please contact author\n"; assertfalse ())
						)
						| _ => () (* Recursion *)
				) (* End of handler *)
			)		
		
		(*
		 * we use dt for functional curry subtyping, which is irrelvant to our main propagation theory
		 * we use dt_sub for functional application subtyping, which is the relvant part to our main propagation theory
		 *)
		fun get_k_deps refcons dt dt_sub orig = 
			case refcons of 
				  SubRef (env, g, (subs, qe), (_,F.Qvar (kr, _)), funflag, _, _, _, _) => (
					let val kls = iter_get_k_deps env subs qe
						val lcns = HashTable.lookup orig (get_ref_id refcons) handle Not_found => (print "ERROR: get_ref_orig"; raise Not_found)
	  				in  
	  					if (funflag) then (* Track subtyping relations we only want to track functional subtyping chains *)
		  					(case (Exp.node (get (simplylc lcns))) of 
		  						  Exp.App _ => (* application related subtyping *)
		  						  	if (HashTable.inDomain dt_sub kr) then
										let val klist = HashTable.lookup dt_sub kr
										in HashTable.insert dt_sub (kr, (kls @ klist)) end
									else
										HashTable.insert dt_sub (kr, kls)
		  						| _ => (* curried subtyping *)
									if (HashTable.inDomain dt kr) then
										let val klist = HashTable.lookup dt kr
										in HashTable.insert dt (kr, (kls @ klist)) end
									else
										HashTable.insert dt (kr, kls)	  
							) handle RuntimeExecption => (  (* Recursive function frames subtyping has no exp specified *)
								if (HashTable.inDomain dt kr) then
									let val klist = HashTable.lookup dt kr
									in HashTable.insert dt (kr, (kls @ klist)) end
								else
									HashTable.insert dt (kr, kls)
							)				
						else case (Exp.node (get (simplylc lcns))) of
							Exp.Record _ => 
								if (HashTable.inDomain dt kr) then
									let val klist = HashTable.lookup dt kr
									in HashTable.insert dt (kr, (kls @ klist)) end
								else
									HashTable.insert dt (kr, kls)
							| _ => ()  
	  				end
				)
				| _ => ()
				
		
		(* om is labeled constraint hash table; cm is refinement constraint hash table; 
		 * VM is a path.t map. 
		 * Collect the refinements in each refinement constraint (only appeared on the left end)
		 * km indexed by refinements is such a map whose value it the set of constraint ids.
		 * dm is then a map indexed by refinement contraints id, the value is a collections of constraint id
		 * whoes mapping constraints refer to the refinements appeared in this constraint's right end on
		 * their left end.
		 * deps is a list of pairs <id, id'> in which id is the constraint use a refinement in its right.
		 * while id' is the constraint use the same refinement in its left.
		 * Using deps, we can calcuate scc graph and assign each constraint a rank.
		 * rank is stored in rm together with labeled constraint id and a bool value indicating if it has pending substitution
		 *) 
		 
		fun make_rank_map om cm =
  			let 
  				val initial_size = 37
  				val evm = mkTable (hash_fn o (Var.toString), Var.logic_equals) (initial_size, Not_found)
  				val edm = mkTable (hash_fn o (Int.toString), (op=)) (initial_size, Not_found)
  				val erm = mkTable (hash_fn o (Int.toString), (op=)) (initial_size, Not_found)
  				val erkm = mkTable (hash_fn o (Var.toString), Var.logic_equals) (initial_size, Not_found)
  				fun get k vm = HashTable.lookup vm k handle Not_found => []
	  			fun upd id (k, vm) = (HashTable.insert vm (k, (id::(get k vm))); vm)
	   			val km = HashTable.foldi (fn (id, c, vm) => case c of 
	   				   WFRef _ => vm
	   				| SubRef _ => List.fold ((lhs_ks c), vm, (upd id))) evm cm
				val (dm,deps) = HashTable.foldi (fn (id, c, (dm, deps)) => case (c, rhs_k c) of
						(WFRef _, _) => (dm, deps)
						| (_, NONE) => (dm, (id, id) :: deps)
						| (_, SOME k) => 
							let val kds = get k km 
								val deps' = List.map ((id :: kds), (fn id' => (id, id')))	
							in (((*print ("\n id " ^ (Int.toString id) ^ " kds: " ^ List.fold (kds, "", fn (k, str) => str ^ (Int.toString k) ^ " ") 
							^"\n");*) HashTable.insert dm (id, kds); dm), List.appendRev (deps, deps')) end) (edm, []) cm
				(* fun flabel i = C.io_to_string (case (HashTable.find om i) of lc c' => #lc_id c' | _ => assertfalse()) *)
				val rm = List.fold ((C.scc_rank deps), erm, 
					(fn ((id, r), rm) => 
						let val b = (not (!Cf.psimple)) orelse (is_simple_constraint (HashTable.lookup cm id))
				        	val fci = (case (HashTable.lookup om id) of lc c' => #lc_id c')
				        in (HashTable.insert rm (id, (r, b, fci)); rm) end))
				        
				val rkm = HashTable.foldi (fn (id, c, vm) => case c of 
	   				   WFRef _ => vm
	   				| SubRef _ => case (rhs_k c) of SOME k => upd id (k, vm) | NONE => vm) erkm cm
			in
	  			(dm,rm,rkm)
	  		end
		
		val fresh_refc = 
			let val i = ref 0
			in
		  		fn c => 
		  			let val i' = (incr i; !i)
		  			in	 
				    	case c of  
				    		  WFRef (env,r,None) => WFRef (env,r,SOME i')
				    		| SubRef (env,g,r1,r2,flag,ri,con,conri,None) => SubRef (env,g,r1,r2,flag,ri,con,conri,SOME i')
				    end
			end
		
		(* API: store the frame constraints in om and refinement constraints translated from frames in cm *)
		fun make_ref_index ocs = 
			let
				val initial_size = 37 
				val om = HashTable.mkTable (hash_fn o (Int.toString), (op=)) (initial_size, Not_found)
				val cm = HashTable.mkTable (hash_fn o (Int.toString), (op=)) (initial_size, Not_found)
				val kdeps = HashTable.mkTable (hash_fn o (Var.toString), Var.logic_equals) (initial_size, Not_found)
				val kdeps_2 = HashTable.mkTable (hash_fn o (Var.toString), Var.logic_equals) (initial_size, Not_found)
				val ics = List.map (ocs, (fn (o',c) => (o',fresh_refc c))) 
				val pendm = HashTable.mkTable (hash_fn o (Int.toString), (op=)) (initial_size, Not_found)
				val pcks = HashTable.mkTable (hash_fn o (Var.toString), Var.logic_equals) (initial_size, Not_found)
			in
				(List.foreach(ics, (fn (o', c) => 
					let val o' = case o' of Cstr fc => fc | _ => assertfalse ()
	        			val i = get_ref_id c 
	        		in 
						HashTable.insert om (i, o'); HashTable.insert cm (i, c)
					end));
				List.foreach(ics, fn (o', c) => 
					get_k_deps c kdeps kdeps_2 om
				);
				(*print "---------print deps-------------------";
				List.foreach (HashTable.listItemsi kdeps, fn (a, b) => 
				print ("\n" ^ (Var.toString a) ^ "->" ^ (List.fold (b, "", fn (bi, str) => ((Var.toString bi) ^ " " ^ str))) ^"\n"));*)
		  		let val (dm,rm,rkm) = make_rank_map om cm 
		  		in {orig = om, cnst = cm, rank = rm, depm = dm, pend = pendm, 
		  				rhs_km = rkm, curried_k_deps = kdeps, app_k_deps=kdeps_2, postcondition_ks=pcks} end)
		  	end
		
		fun get_ref_orig {orig=orig',cnst=cnst',rank=rank',depm=depm',pend=pend',
							rhs_km=rhs_km',curried_k_deps=curried_k_deps', app_k_deps=app_k_deps', postcondition_ks=postcondition_ks'} c = 
			HashTable.lookup orig' (get_ref_id c) handle Not_found => (print "ERROR: get_ref_orig"; raise Not_found)
		  
		(* API: If one constraint is updated, we get all the constraints dependent on it*)
		fun get_ref_deps (sri as {orig=orig',cnst=cnst',rank=rank',depm=depm',pend=pend',
							rhs_km=rhs_km',curried_k_deps=curried_k_deps', app_k_deps=app_k_deps', postcondition_ks=postcondition_ks'}) c =
			let val is' = HashTable.lookup depm' (get_ref_id c) handle Not_found => []
			in List.map (is', (get_ref_constraint sri)) end
		
		(* API: get all refinement constraints *)
		fun get_ref_constraints {orig=orig',cnst=cnst',rank=rank',depm=depm',pend=pend',
							rhs_km=rhs_km',curried_k_deps=curried_k_deps', app_k_deps=app_k_deps', postcondition_ks=postcondition_ks'} = 
			HashTable.foldi (fn (_, c, cs) => c::cs) [] cnst'
		
		(* API *)
		fun iter_ref_constraints {orig=orig',cnst=cnst',rank=rank',depm=depm',pend=pend',
							rhs_km=rhs_km',curried_k_deps=curried_k_deps', app_k_deps=app_k_deps', postcondition_ks=postcondition_ks'} f = 
			let val li = HashTable.listItemsi cnst'
			in
				List.foreach (li, (fn ((_, c)) => f c))
			end
		
		(* API *)
		fun push_worklist (sri as {orig=orig',cnst=cnst',rank=rank',depm=depm',pend=pend',
							rhs_km=rhs_km',curried_k_deps=curried_k_deps', app_k_deps=app_k_deps', postcondition_ks=postcondition_ks'}) w cs =
			List.fold (cs, w, (fn (c, w) => 
				let val id = get_ref_id c 
				in
					case (HashTable.find pend' id) of
						  SOME _ => w
						| NONE => 
							let val _ = HashTable.insert pend' (id, ()) 
							in WH.add (id, get_ref_rank sri c) w end
				end
				))
						
		(* API *)
		fun pop_worklist (sri as {orig=orig',cnst=cnst',rank=rank',depm=depm',pend=pend',
							rhs_km=rhs_km',curried_k_deps=curried_k_deps', app_k_deps=app_k_deps', postcondition_ks=postcondition_ks'}) w =
			(let val id = (fn (a, b) => a) (WH.maximum w)
				 val _ = (HashTable.remove pend' id) handle Not_found => (print "Reverifiying a constraint due to new precondition set.\n")
			in
				(SOME (get_ref_constraint sri id), WH.remove w)
			end)
			handle WH.EmptyHeap => (NONE, w)
		
		(* API *)
		fun make_initial_worklist sri = 
			let val cs = List.keepAll ((get_ref_constraints sri), is_subref_constraint)
			in
				HashTable.clear (#pend sri);
				push_worklist sri WH.empty cs
			end
		
		
		(* Return also a postcondition ks *)	
		fun split_lcs cs postcondition_ks = 
			let (* Record all postcondition in  *)
				val _ = get_postcondition_ks cs postcondition_ks
				val r = split cs
				val _ = print "\nsplited\n"
			in make_ref_index r end
			(*let val cs = if !Cf.simpguard then List.map (cs, simplify_fc) else cs
			in make_ref_index (split cs) end*)
			
		
		(**************************************************************)
		(********************* Constraint & Frame *********************)
		(**************************************************************)
		fun genParAppSubs fr funvar =
			let fun genSubs fr index = 
					case fr of 
						Frame.Farrow (l, f, f') => (case l of 
							SOME pat => ( 
								let val v = case (Pat.node pat) of 
									Pat.Var v => v
									| _ => (print "\nTool fail to verify record feature\n"; assertfalse ())
								in (v, Predicate.FunApp (("arg" ^ (Int.toString index)), [Predicate.PVar funvar])) :: (genSubs f' (index+1)) end
							)
							| NONE => []
						)
						| _ => []
			in genSubs fr 0 end	
		
		(* The real entity of a guard is embedded into light env. 
		 *)
		fun guard_predicate () g = 
		  P.big_and 
		    (List.map (
		      g, (fn (v,b, flag) => 
		      		if flag then P.equals (B.tag (P.PVar v)) (P.PInt b)	else P.equals ((P.PVar v)) (P.PInt b)
		         (*let val p = P.equals (B.tag (P.PVar v)) (P.PInt 1) in
		         if b then p else (P.Not p) end*))))
		  
		(*fun qual_to_pred quals qual_expr subs = 
			let val _ = print ("\n...... qual_expr is " ^ (Predicate.pprint_pexpr qual_expr) ^ "......\n")
				val unsubst = List.map (quals, (Qualifier.apply qual_expr)) 
			in
				print ("\n;;;;;;" ^ (List.fold (quals, "", fn ((v1,v2,pred), str) => (str ^ (Predicate.pprint pred)))) ^ ";;;;;\n");
				print ("\n;;;;;;" ^ (List.fold (unsubst, "", fn (pred, str) => (str ^ (Predicate.pprint pred)))) ^ ";;;;;\n");
		    	List.map (unsubst, (Predicate.apply_substs subs))
		    end
		*)
		
		fun qual_to_pred quals qual_expr subs = 
			let val subst = List.map (quals, fn (v1, v2, p) => (v1, v2, (Predicate.apply_substs subs p)))
			in
		    	List.map (subst, (Qualifier.apply qual_expr))   
		    end
		
		(*fun c_qual_to_pred quals qual_expr subs = 
			let val subst = List.map (quals, fn (v1, v2, p) => (v1, v2, (Predicate.apply_substs subs p)))
			in 
				if (Predicate.logic_equals_pexpr qual_expr qual_test_expr) then List.map subst
				else 
					List.map (subst, (Qualifier.apply qual_expr))  
			end   *)
		
		fun predicate sri solution qual_expr f envpending conpending refvarpending polymatching_table ifb =
		  Predicate.big_and (conjuncts sri solution qual_expr f envpending conpending refvarpending polymatching_table ifb)
		
		and conjuncts sri solution qual_expr fr envpending conpending refvarpending polymatching_table ifb =
		  conjunct_fold [] sri solution qual_expr fr envpending conpending refvarpending polymatching_table ifb
		
		and conjunct_fold cs sri solution qual_expr fr envpending conpending refvarpending polymatching_table ifb = (
			case fr of 
				  F.Fconstr(_, _, r) => refinement_conjuncts sri solution qual_expr r false envpending conpending refvarpending polymatching_table ifb @ cs
				| F.Fsum (_, _, r) => refinement_conjuncts sri solution qual_expr r false envpending conpending refvarpending polymatching_table ifb @ cs
		  		| F.Frecord (fs, r) =>
		        	let fun subframe_fold envpending conpending refvarpending polymatching_table ifb ((f, name), b) = 
		        		conjunct_fold b sri solution (Predicate.Field (name, qual_expr)) f envpending conpending refvarpending polymatching_table ifb
		      		in (refinement_conjuncts sri solution qual_expr r false envpending conpending refvarpending polymatching_table ifb) 
		      			@ (List.fold (fs, cs, (subframe_fold envpending conpending refvarpending polymatching_table ifb)))
		      		end
		      	| F.Fvar (_, r) => refinement_conjuncts sri solution qual_expr r false envpending conpending refvarpending polymatching_table ifb @ cs
		      	| F.Farrow (NONE, f1, f2) => 
		      		let val paramvars = Frame.hofunFramevars fr (
		      				case qual_expr of
		      					Predicate.PVar var => var
		      					| _ => (print "\nhigher order function representation error\n"; assertfalse ())
		      			)
		      			val fr = Frame.getFrowFr fr
		      		in conjunct_fold cs sri solution (Predicate.FunApp ("P" ^ (Int.toString (List.length paramvars)), (qual_expr) :: paramvars)) 
		      			fr envpending conpending refvarpending polymatching_table ifb end
		  		| _ => cs
		)
		and refinement_conjuncts (sri as {orig=orig',cnst=cnst',rank=rank',depm=depm',pend=pend',
						rhs_km=rhs_km',curried_k_deps=curried_k_deps', app_k_deps=app_k_deps', postcondition_ks=postcondition_ks'}) 
							solution qual_expr (subs, qualifier) funflag 
							envpending conpending refvarpending polymatching_table ifb =
			case qualifier of
		    	  F.Qvar (k, _) => (
		    		(let val qs = (solution k) 
		    		in qual_to_pred qs qual_expr subs end)
		    		handle RuntimeError => (
						if (HashTable.inDomain refvarpending k) then []
						else (	    		
			    			HashTable.insert refvarpending (k, ());
			    			if funflag then ( 
			    				if (HashTable.inDomain polymatching_table k) then 
			    					let val k' = HashTable.lookup polymatching_table k
			    					in qual_to_pred (solution k') qual_expr subs end handle RuntimeError => []
			    				else []
			    			)
			    			else (
			    				case HashTable.find rhs_km' k of 
				    	  		  SOME ids => 
				    	  		  	if ((List.length ids) > 1) then
					    	  		  	let val preds = List.map (ids, fn (id) => 
					    	  		  		let val p = HashTable.lookup cnst' id
					    	  		  		in
					    	  		  			(HashTable.insert conpending (id, ());
					    	  		  			case p of
					    	  		  				  SubRef (env,g,r1, (sub2s, F.Qvar (k2, _)), funflag, _, _, _, _) =>
					    	  		  				 	let val (r1p, thep) = path_sensitive_implies_pred sri env g solution r1 funflag qual_expr 
					    	  		  				 							envpending conpending refvarpending polymatching_table ifb
					    	  		  				 	in thep end
					    	  		  				| _ => assertfalse ())
					    	  		  		end)
					    	  		  	in
					    	  		  		[Predicate.apply_substs subs (P.big_and preds)]
					    	  		  	end
				    	  		  	else 
				    	  		  		let val id = List.first ids
				    	  		  		 	val _ = HashTable.insert conpending (id, ())
				    	  		  			val p = HashTable.lookup cnst' id
				    	  		  			val pred = 
					    	  		  			case p of
					    	  		  				  SubRef (env,g,r1, (sub2s, F.Qvar (k2, _)), funflag, _, _, _, _) =>
					    	  		  				 	let (*val _ = print ("\nVar " ^ (Var.toString k) ^ " is unfound, get to use ")
															val _ = case r1 of 
																(sub2s, F.Qconst qs) => 
																List.foreach (qs, fn (v1, v2, p) => print (" " ^ (Predicate.pprint p) ^ ", "))
																| (sub2s, F.Qvar (k2, _)) => 
																(List.foreach (solution k2, fn (v1, v2, p) => 
																print ("k is " ^ (Var.toString k2) ^ " "  ^ (Predicate.pprint p) ^ ", ")))
																handle RuntimeError => print " undefined now "
															val _ = print "\n"*)
					    	  		  				 		val (r1p, thep) = implies_pred sri env g solution r1 funflag qual_expr 
					    	  		  				 			envpending conpending refvarpending polymatching_table ifb
					    	  		  				 	in thep end
					    	  		  				| _ => assertfalse ()
				    	  		  		in [Predicate.apply_substs subs pred] end
				    	  		| NONE => ((*print ("\n\n" ^ (Var.toString k) ^ "Is not a function input but has no predicated attached \n\n"); *)
				    	  					if (HashTable.inDomain polymatching_table k) then 
				    	  						qual_to_pred ((solution (HashTable.lookup polymatching_table k)) handle RuntimeError => []) qual_expr subs
				    	  					else qual_to_pred [] qual_expr subs)
			    			) (* End of second else *)
				    	) (* End of frist else*)
			    	) (* Endo of handle Runtime Error*)
		    	  ) (* End of F.Qvar *)
		    	| F.Qconst qs => qual_to_pred qs qual_expr subs

		and implies_pred sri env g sm r1 funflag qual_test_expr envpending conpending refvarpending polymatching_table ifb = 
			let val gp = (guard_predicate ()) g
				(*val _ = print ("predicate gp is " ^ (Predicate.pprint gp)) *)
				val envp = (environment_predicate sri sm) env envpending conpending refvarpending polymatching_table ifb false
				(*val _ = print ("envp is " ^ (Predicate.pprint envp) ^ "\n") *)
				val r1p = (refinement_predicate sri sm qual_test_expr) r1 funflag envpending conpending refvarpending polymatching_table ifb
				
				(*val _ = print ("r1p is " ^ (Predicate.pprint r1p) ^ "\n") *)
			in
				(r1p, P.big_and [envp, gp, r1p])
			end
		
		and path_sensitive_implies_pred sri env g sm r1 funflag qual_test_expr envpending conpending refvarpending polymatching_table ifb = 
			let val gp = (guard_predicate ()) g
				(*val _ = print ("predicate gp is " ^ (Predicate.pprint gp)) *)
				val envp = (environment_predicate sri sm) env envpending conpending refvarpending polymatching_table ifb true
				(*val _ = print ("envp is " ^ (Predicate.pprint envp) ^ "\n") *)
				val r1p = (refinement_predicate sri sm qual_test_expr) r1 funflag envpending conpending refvarpending polymatching_table ifb
				(*val _ = print ("r1p is " ^ (Predicate.pprint r1p) ^ "\n") *)
			in
				(r1p, P.big_and [envp, (P.imply gp r1p)])
			end
			
		(* Predicates conjunction of light env *)
		and environment_predicate sri sm env envpending conpending refvarpending polymatching_table ifb flag =
		  P.big_and (Le.maplistfilter (fn v => fn fr => 
		  				if (HashTable.inDomain envpending v) then NONE
		  				else (HashTable.insert envpending (v, fr);
		  					(*print ("\nFrom env, dealing with variable " ^ (Var.toString v) ^ " with frame as " ^ (Frame.pprint_final fr sm) ^ "\n");*)
		  					if flag then (
		  						if (String.hasPrefix (Var.toString v, {prefix = "constructor"})) then NONE
		  						else (
		  							let val p = (predicate sri sm (P.PVar v) fr envpending conpending refvarpending polymatching_table ifb)
			  							val p = 
			  								if (HashTable.inDomain ifb v) then
			  								 	Predicate.big_and [p, 
			  								 		let val vp = (HashTable.lookup ifb v)
			  								 		in
			  								 			case vp of
			  								 				Predicate.True => (* We have claimed that this is higher order function *)
			  								 					let val subs = genParAppSubs fr (v)
			  								 						val returnfr = Frame.getFrowFr fr
			  								 						val returnfr = List.fold (subs, returnfr, fn (sub, returnfr) => 
			  								 							Frame.apply_substitution sub returnfr
			  								 						)  
			  								 						
			  								 						val paramvars = Frame.hofunFramevars fr (v)
			  								 						
			  								 						(*val vp = Predicate.big_and (conjunct_fold [] sri sm (Predicate.FunApp ("P1", (Predicate.PVar v) :: paramvars)) 
			  								 									returnfr envpending conpending refvarpending polymatching_table ifb)
			  								 						*)
			  								 						val vp = predicate sri sm (Predicate.FunApp ("P" ^ (Int.toString (List.length paramvars)), (Predicate.PVar v) :: paramvars)) 
			  								 									returnfr envpending conpending refvarpending polymatching_table ifb
			  								 					in vp end
			  								 				| _ => vp
			  								 		end
			  								 	]
			  								 else p
		  								(*val _ = print ("\nthe predicate obtained is " ^ (Predicate.pprint p) ^ "\n")*)
		  							in SOME p end
		  						) 
		  					)
		  					else
		  						let val p = (predicate sri sm (P.PVar v) fr envpending conpending refvarpending polymatching_table ifb)
		  							(*val _ = print ("\n1.the predicate obtained is " ^ (Predicate.pprint p) ^ "\n")*)
		  							val p = 
			  								if (HashTable.inDomain ifb v) then
			  								 	Predicate.big_and [p, 
			  								 		let val vp = (HashTable.lookup ifb v)
			  								 		in
			  								 			case vp of
			  								 				Predicate.True => (* We have claimed that this is higher order function *)
			  								 					let (*val _ = print "\nPredicate.True obtained\n"*)
			  								 						val subs = genParAppSubs fr (v)
			  								 						val returnfr = Frame.getFrowFr fr
			  								 						val returnfr = List.fold (subs, returnfr, fn (sub, returnfr) => 
			  								 							Frame.apply_substitution sub returnfr
			  								 						)  
			  								 						
			  								 						val paramvars = Frame.hofunFramevars fr (v)
			  								 						
			  								 						val vp = Predicate.big_and (conjunct_fold [] sri sm (Predicate.FunApp ("P" ^ (Int.toString (List.length paramvars)), 
			  								 									(Predicate.PVar v) :: paramvars)) 
			  								 									returnfr envpending conpending refvarpending polymatching_table ifb)
			  								 					in vp end
			  								 				| _ => vp
			  								 		end
			  								 	]
			  								 else p
		  							(*val _ = print ("\n2.the predicate obtained is " ^ (Predicate.pprint p) ^ "\n")*)
		  						in SOME p end
		  					)) env)
				
		(* The following functions making the predicate conjunctions for one refinement *)
		and refinement_predicate sri solution qual_var refn funflag envpending conpending refvarpending polymatching_table ifb =
			Predicate.big_and (refinement_conjuncts sri solution qual_var refn funflag envpending conpending refvarpending polymatching_table ifb)
					
			
		
		fun pprint_local_binding (k, v) = ((Var.toString k) ^ " binds to " ^ (F.pprint v))
	
		(*fun pprint_env_pred sri so env =
			case so of 
				  SOME s => P.pprint (environment_predicate sri (solution_map s) env (HashTable.mkTable (hash_fn o (Var.toString), Var.logic_equals) (17, Not_found)))
				| _ => Le.fold (fn x => fn t => fn str => str ^ (pprint_local_binding (x, t)) ^ "\n\n") env ""
		*)		
		fun pprint_pure_env env = 
			Le.fold (fn x => fn t => fn str => str ^ (pprint_local_binding (x, t)) ^ "\n\n") env ""
		  
		  
		(**************************************************************)
		(********************** Pretty Printing ***********************)
		(**************************************************************)
								  		
		 (*fun pprint_refinement_with_solution refi sri solution =
		  	let val qual_expr = Predicate.PVar (Var.fromString "AA")
		  	in
		 		Predicate.pprint (Predicate.big_and (refinement_conjuncts sri solution qual_expr refi))
			end
			
		fun pprint_with_solution frame sri solution = 
		 	case frame of 
				  F.Fvar (a, _) => "Var(" ^ (F.unique_name a) ^ ")"
		  		| F.Fconstr (path, [], r) => "@[constructor " ^ (Tycon.toString path) ^
		  									" refinement "  ^ (pprint_refinement_with_solution r sri solution) ^ "@]" 
		  		| F.Farrow (NONE, f, f') => "@[param: " ^ (pprint_with_solution1 f sri solution) ^ " -> retval: " ^ (pprint_with_solution1 f' sri solution) ^ "@]"
		  		| F.Farrow (SOME pat, f, f') => "@[pat: " ^ (F.pprint_pattern pat) ^ " param: " ^ (pprint_with_solution1 f sri solution) 
		  										^ "-> retval: " ^ (pprint_with_solution1 f' sri solution) ^ "@]"
		  		| F.Fconstr (path, l, r) => "@[constructor " ^ (Tycon.toString path) ^ " type_expr_li " ^ (pprint_with_solution_list "," l sri solution) ^ 
		  									" refinement " ^ (pprint_refinement_with_solution r sri solution) ^ "@]"
		  		| F.Frecord (l, r) => "@[Record param list " ^ (pprint_with_solution_list2 "*" l sri solution) ^ 
		  									" refinement " ^ (pprint_refinement_with_solution r sri solution) ^ "@]"
		  		| F.Funknown => "@[unknown@]"
		  		
		 and pprint_with_solution1 f sri sol = 
		 	case f of 
		 		  f as (F.Farrow _) => "@[(" ^ (pprint_with_solution f sri sol) ^ ")@]" 
		 		| f as _  => pprint_with_solution f sri sol
		 and pprint_with_solution_list sep fs sri sol = List.fold (fs, "", (fn (f, str) => (str ^ (pprint_with_solution f sri sol) ^ sep))) 
		 and pprint_with_solution_list2 sep fs sri sol = List.fold (fs, "", (fn ((f, field), str) => 
		 	(str ^ " " ^ field ^ " " ^ (pprint_with_solution f sri sol) ^ sep))) 
		 	
		 	*)
		(**************************************************************)
		(****************** Debug/Profile Information *****************)
		(**************************************************************)
		
		(* print all constraints *) 
		fun dump_constraints sri = 
		  if !Cf.dump_constraints 
		  then
				(print "@[Refinement Constraints@.@\n@]";
		  		iter_ref_constraints sri (fn c => print ("@" ^ ((pprint_ref NONE) c) ^ "@.@]")))
		  else ()
		  
		  
		fun getExp 
			(sri as {orig=orig',cnst=cnst',rank=rank',depm=depm',pend=pend',rhs_km=rhs_km',
			curried_k_deps=curried_k_deps',app_k_deps=app_k_deps', postcondition_ks=postcondition_ks'}) refcns =
			let val lcns = get_ref_orig sri refcns
				fun simplylc c = case c of lc c' => c'
				fun get cstr' =
			    	case #lc_orig cstr' of
				        Loc exp => (case exp of SOME exp => exp | NONE => (print "constraint with out specific expression\n"; assertfalse ()))
				      | Assert exp => exp
				      | Cstr cstr => get (simplylc cstr)
		  	in get (simplylc lcns) end
		(* 
		fun getRelated dt k = 
			let val rdt = HashTable.mkTable (hash_fn o (Var.toString), Var.logic_equals) (HashTable.numItems dt, Not_found)
				val _ = List.foreach (HashTable.listItemsi dt, fn (a, b) =>  (
					List.foreach (b, fn b' => 
						if (HashTable.inDomain rdt b') then
							let val li = HashTable.lookup rdt b' 
							in HashTable.insert rdt (b', (a :: li)) end
						else
							HashTable.insert rdt (b', [a])
						)
					)
				)
				fun getKs k m = 
					if (HashTable.inDomain m k) then
						let val k' = HashTable.lookup m k
						in k' :: (getKs k' m) end
					else []
				fun getKs' k m = 
					if (HashTable.inDomain m k) then
						let val ks' = HashTable.lookup m k
						in 
							List.fold (ks', ks', fn (lk, ks') => (getKs' lk m @ ks'))
						end
					else []
			in
				(getKs k dt) @ (getKs' k rdt)
			end	  *)	
		  	
		(* 
		 * Get refinement k's refinement chain list
		 * This function is called when setting a functional refinement or setting a precondition
		 *)  	
		fun getCurriedKs (sri as {orig=orig',cnst=cnst',rank=rank',depm=depm',pend=pend',
							rhs_km=rhs_km',curried_k_deps=curried_k_deps', app_k_deps=app_k_deps', postcondition_ks=postcondition_ks'}) k = 
			let val r_curried_k_deps' = 
				HashTable.mkTable (hash_fn o (Var.toString), Var.logic_equals) 
				(HashTable.numItems curried_k_deps', Not_found)
				val _ = List.foreach (HashTable.listItemsi curried_k_deps', fn (a, b) =>  (
					List.foreach (b, fn b' => 
						if (HashTable.inDomain r_curried_k_deps' b') then
							let val li = HashTable.lookup r_curried_k_deps' b' 
							in HashTable.insert r_curried_k_deps' (b', (a :: li)) end
						else
							HashTable.insert r_curried_k_deps' (b', [a])
						)
					)
				)
				val cache = HashTable.mkTable (hash_fn o (Var.toString), Var.logic_equals) (17, Not_found)
				fun getKs k m = (  
					if (HashTable.inDomain m k andalso (not (HashTable.inDomain cache k))) then
						let val ks = HashTable.lookup m k
							val _ = HashTable.insert cache (k, ())
						in 
							List.fold (ks, ks, fn (lk, ks) => ((getKs lk m @ ks)))
						end
					else []
				)
				val l1 = 
					if (HashTable.inDomain curried_k_deps' k) then (
						HashTable.clear cache;
						getKs k curried_k_deps'
					)
					else []
				val l2 = 
					if (HashTable.inDomain r_curried_k_deps' k) then (
						HashTable.clear cache;
						getKs k r_curried_k_deps'
					)
					else []
			in
				l1 @ l2
			end
		(*
		fun getAppKs (sri as {orig=orig',cnst=cnst',rank=rank',depm=depm',pend=pend',
						rhs_km=rhs_km',curried_k_deps=curried_k_deps', app_k_deps=app_k_deps', postcondition_ks=postcondition_ks'}) k = 
			getRelated app_k_deps' k
		*)
		fun getPostconditionKs (sri as {orig=orig',cnst=cnst',rank=rank',depm=depm',pend=pend',
						rhs_km=rhs_km',curried_k_deps=curried_k_deps', app_k_deps=app_k_deps', postcondition_ks=postcondition_ks'}) = 
			postcondition_ks'
	end
