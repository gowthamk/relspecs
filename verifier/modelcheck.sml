(* Author: G
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
    structure SIM = IntMap
    structure VM = VarMap
		
		type binding_id = int
		
		(*type binding_cnst = VerificationCondition.binding_cnst*)
		
		(* Modular top level bindings of sml program *)
			
		open RelConstraint

    (*fun instantiate_in_environments rcs rqs tm = 
    let
      fun inst_qual_for_cstr q rc =
        let
          val (env,ty) = case rc of
              SubRFrame ((e,_,_),f1,f2) => (e,shape f2)
            | WFRFrame ((e,_,_),f) => (e,shape f)
          fun get_sl_by_cstr c =
            let
              val formal_tyvs = TM.get_tyvars_by_cstr tm c
              val (tycon,actual_tys) = case ty of 
                  Tconstr(tc,tyvs) => (tc,tyvs) 
                | _ => fail "Tconstr expected\n"
              val _ = assertl (formal_tyvs,actual_tys,"Tycon args mismatch")
              val tyvarmap = List.zip(formal_tyvs,actual_tys)
              val set_formal = List.foldr((TM.get_argtys_by_cstr tm c),[],
                (fn ((t,f),acc) => if(not f) then t::acc else acc))
              val set_actual = List.map (set_formal,
                (fn t => instantiate_type tyvarmap t))
              val set_actual = case set_actual of 
                  [t] => t
                | _ => Ttuple set_actual
              val set_sl = Le.get_vars_by_type env set_actual
              val rec_sl = Le.get_vars_by_type env ty 
            in
              (set_sl,rec_sl)
            end
         fun inst_cstr_rexpr c re q_substf = 
          let
            val cstrs = TyconMap.get_cstrs_by_tycon tm tycon
            val cstr_sl = if (Con.equals(c,Con.fromString "any"))
              then cstrs
              else if(List.exists(cstrs,(fn c' => Con.equals(c,c'))))
              then [c]
              else fail "Invalid constructor\n"
            val inst_qs = List.foldr (cstr_sl, [], 
              (fn (c,acc) => 
                let
                  val (set_sl,rec_sl) = get_sl_by_cstr c
                  val inst_re = instantiate_restricted_rexpr (c,set_sl,rec_sl) re
                in
                  (q_substf c inst_re)::acc
                end))
          in
            inst_qs
          end
          val inst_qs  = case q of 
              (name,bv,RPred (RAtom ((RRel(c,RVar(v))),_,re))) =>
              let
                val _ = asserti (Var.equals (bv,v), "boundvar error\n")
                val q_substf = fn c => fn re => 
                  (name,bv,RPred (RAtom ((RRel(c,RVar(v))),_,re)))
              in
                inst_cstr_rexpr c re q_substf
              end
            | _ => []
        in
          inst_qs
        end
      fun instantiate_quals_for_cstr qs rc = 
        List.fold(qs,[],(fn (q,acc) => acc@(inst_qual_for_cstr q rc)))
    in
      List.map (rcs,(fn rc => inst_quals_for_cstr qs rc))
    end*)

    val fresh_fc_id = 
      let 
        val r = ref 0 
        fun incr i = (i := !i + 1)
      in
        fn () => (incr r; SOME (!r))
      end

    val fresh_refc = 
      let 
        val i = ref 0
        fun incr i = (i := !i + 1)
      in
      fn c => 
        let 
          val i' = (incr i; !i)
        in
          case c of  
            RCs.WFRef (rel_env,r,NONE) => RCs.WFRef (rel_env,r,SOME i')
          | RCs.SubRef (rel_env,r1,r2,NONE) => RCs.SubRef (rel_env,r1,r2,SOME i')
          | _ => assertfalse ()
        end
      end

    fun lhs_ks rc = case rc of
        WFRef _ => assertfalse() 
      | SubRef (rel_env,(_,qe),_,_) =>
        let 
          val (env,renv,g) = rel_env
          val ks = RLe.fold (fn v => fn rf => fn l => RF.refinement_vars rf @ l) renv []
        in
          case qe of RF.RQvar (k, _) => k::ks | _ => ks
        end

    fun rhs_k rc = case rc of
        SubRef (_,_,(_,RF.RQvar (k, _)),_) => SOME k
      | _ => NONE

    fun make_rank_map om cm =
      (* vm : varmap  = path.t map*)
      (* SIM is int-indexed map *)
      let 
        fun get vm k = case VM.find (vm,k) of 
            SOME l => l
          | NONE => []
        fun upd id vm k = VM.insert (vm,k,(id::(get vm k)))
      (* collect all refinement vars of from
         environment referred by constraint. For each 
         refinement var, maintain which constraints it 
         occurs in inside a Path.t => [constraint_ref_id list] map
      *)
        (* var -> constrain_id list dep map *)
        val km = SIM.foldli (* fold increasing order *)
          (fn (id,c,vm) => case c of WFRef _ => vm 
            | SubRef _ => List.fold ((lhs_ks c),vm,(fn(k,vm)=>(upd id vm k))))
          VM.empty cm
      (* dependency map, dependency list : id -> [dependent_id list] *)
        val (dm,deps) = SIM.foldli
          (fn (id,c,(dm,deps)) => 
            case (c, rhs_k c) of 
              (WFRef _,_) => (dm,deps) 
            | (_,NONE) => (dm,(id,id)::deps) 
            | (_,SOME k) => 
              let 
                val kds = get km k 
                val deps' = List.map (id::kds,(fn id' => (id,id')))
              in 
              (* get all constraint_ids where k occurs 
                 as bound ref var inside the antecedent
                 or within the env of constraint.
               *)
              (* foreach such id, mark dependency between
                 current constraint_id and that constraint_id 
               *)
                (SIM.insert (dm,id,kds), (List.rev deps)@deps')
              end)
          (SIM.empty,[]) cm

      (* given ref constraint index, get corresponding labeled constraint id *)
        fun flabel i = Int.toString (case (SIM.find_crash (om,i)) of 
            RCs.lc c => (case #lc_id c of SOME i => i 
              | NONE => assertfalse())
          | _ =>assertfalse())
      (* rm is constraint index => (r,b,fci) map 
         where r is scc_rank
         b <=> constraint being simple
         fci is id of corresponding frame constraint
       *)
        val rm = 
          List.fold ((C.scc_rank deps),SIM.empty,
            (* constraint index, rank of its scc *)
            (fn ((id,r),rm) => 
              let 
                val b = (RCs.is_simple_constraint (SIM.find_crash (cm,id)))
                val fci = case (SIM.find_crash (om,id)) of
                  lc c => #lc_id c
              in
                SIM.insert (rm,id,(r,b,fci))
              end))
      in
        (dm,rm)
      end

    fun get_ref_id rc = case rc of  
        WFRef (_,_,SOME i) => i
      | SubRef (_,_,_,SOME i) => i
      | _ => assertfalse ()

    fun make_ref_index ocs =
      let
        (* freshly number all refinement constraints *)
        val ics = List.map (ocs,(fn (orig,c) => (orig,fresh_refc c)))
        val (om,cm) = List.fold (ics, (SIM.empty,SIM.empty),
          (fn ((orig,c),(om,cm)) => 
            let
              val orig = case orig of RCs.RCstr rfc => rfc 
                | _ => fail "Origin undefined\n"
              val i = get_ref_id c
            in
              (SIM.insert (om,i,orig), SIM.insert (cm,i,c))
            end
          ))
        val _ = print "About to calculate rank map..\n"
        val (dm,rm) = make_rank_map om cm
        val _ = print "Done calculating rank map\n"
      in
        {orig = om, cnst = cm, rank = rm, depm = dm(*, pend = Hashtbl.create 17*)}
      end

    fun pprint_sri {orig=om, cnst=cm, rank=rm, depm=dm} = 
      SIM.foldli (fn (id,rc,_) => 
        let
          val opt = SIM.find (rm,id) (*rm has no WFR constraints*)
          val _ = case opt of
              SOME (r,b,fci) => print ((Int.toString id)^". [rank# "^(Int.toString r)^"]"^
              " - "^(RCs.pprint_ref rc)^"\n")
            | NONE => print ((Int.toString id)^".             "^(RCs.pprint_ref rc)^"\n")
        in
          ()
        end
      ) () cm

    fun solve inst_rqs rcs = 
      let
        val rcs = List.map (rcs,RCs.simplify_rfc)
        val sri = make_ref_index (RCs.split rcs) 
        val _  = pprint_sri sri
      in
        ()
      end
		
		(*
		 * @type qualify_implementation: Lightenv.t => Lightenv.t => Dec.t list => unit
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
				
				val polymatching_table = HashTable.mkTable (hash_fn o (Var.toString), Var.logic_equals) (117, Not_found)
				
				val (fenv, renv, cs, rcs, tm) = RelConstraintgen.constrain_structure fenv renv [] str polymatching_table

				(* Constraints with additional frames given by user or third party tools *)
				(* val cs = (List.map ((Le.maplistfilter (mfm fenv) ifenv), (lbl_dummy_cstr))) @ cs *)
				val _ = print ("\nThe inferred constraints with a total number of " ^ (Int.toString (List.length cs)) ^ " are shown below \n")
				val _ = List.foreachi (cs, (fn (i,c) => 
						(print (Int.toString i); print ": "; print (Constraint.pprint (case c of Cs.lc c' => #lc_cstr c')); print "\n")))
				val _ = print ("the final env is " ^ Constraint.pprint_pure_env fenv)
        val _ = print "**********************************************************\n"
        val _ = print ("Relational Constrains ["^(Int.toString (List.length rcs))^"] are shown below \n")
				val _ = List.foreachi (rcs, (fn (i,c) => 
						(print (Int.toString i); print ": "; print (RCs.pprint (case c of RCs.lc c' => #lc_cstr c')); print "\n")))
				val _ = print ("the final relational env is " ^ RCs.pprint_pure_renv renv)
        val _ = print ("*********************************************************\n\n")
        val rqs = RB.qualifiers()
        (*val inst_rqs = instantiate_in_environments rcs rqs tm*)
        val s = solve rqs rcs
      in
        ()
      end
	end
