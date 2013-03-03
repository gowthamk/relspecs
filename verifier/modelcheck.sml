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
  open RelPredicate

  structure RF = RelFrame
  structure RQ = RelQualifier
  structure Cs = Constraint
  structure RCs = RelConstraint
  structure SIM = IntMap
  structure VM = VarMap
  structure Sol = VarTable
  structure TM = TyconMap

  structure WH = Functional(
    struct 
        type t = RCs.subref_id * (int * bool * RCs.fc_id) 
        fun compare (_, (i, id)) (_, (i', id')) = 
          if i <> i' then
            if i < i' then 1 else ~1
          else 
            case (Int.compare(id, id')) of
                EQUAL => 0
              | LESS => 1
              | GREAT => ~1
    end)

    
  open RelConstraint


  fun instantiate_in_environment envir rqs= 
  let
    val (env,renv,g,tm,f) = envir
    fun inst_qual_in_envir envir q =
      let
        val RF.RFconstr(tycon,tyvrfs,_) = f
        fun get_sl_by_cstr c =
          let
            val tyvs = TM.get_tyvars_by_cstr tm c
            val _ = assertl (tyvs,tyvrfs,"Tycon args mismatch")
            val tyvarmap = List.zip(tyvs,tyvrfs)
            val set_types = List.foldr((TM.get_argtys_by_cstr tm c),[],
              (fn ((t,f),acc) => if(not f) then t::acc else acc))
            val set_type = case set_types of
                [t] => t
              | _ => Type_desc.makeTtuple set_types
            val set_frame =  RF.fresh_with_var_fun (ref tyvarmap)
              set_type (fn _ => RF.empty_refinement) tm
            val set_sl = RLe.get_vars_with_same_shape renv set_frame
            val rec_sl = RLe.get_vars_with_same_shape renv f 
          in
            (set_sl,rec_sl)
          end
       fun inst_cstr_rexpr c re q_substf = 
          let
            val RF.RFconstr(tycon,_,_) = f
            (* remove nullary constructors *)
            val cstrs = #no (List.partition(TM.get_cstrs_by_tycon tm tycon,
              (fn(c)=>(List.length (TM.get_argtys_by_cstr tm c)=0))))
            val cstr_sl = if (Con.equals(c,Con.defaultCons))
              then cstrs
              else if(List.exists(cstrs,(fn c' => Con.equals(c,c'))))
              then [c]
              else fail ("Invalid constructor - "^(Con.toString c)^"\n")
          in
            List.foldr (cstr_sl, [], 
              (fn (c,acc) => 
                let
                  val (set_sl,rec_sl) = get_sl_by_cstr c
                  val inst_rexps = RP.instantiate_restricted_rexpr (c,set_sl,rec_sl) re
                in
                  List.fold (inst_rexps,acc,
                    (fn(inst_rexp,acc)=>(q_substf c inst_rexp)::acc))
                end))
          end
      in
        case q of 
            (name,bv,RPred (RAtom ((RRel(c,v)),rop,re))) =>
            let
              val _ = asserti (Var.equals (bv,v), "boundvar error\n")
              val q_substf = fn c => fn re => 
                (name,bv,RPred (RAtom ((RRel(c,v)),rop,re)))
            in
              inst_cstr_rexpr c re q_substf
            end
          | _ => []
      end
  in
    case f of 
      RF.RFconstr (_,_,_) => List.fold(rqs,[],
        (fn (q,acc) => acc@(inst_qual_in_envir envir q)))
    | _ => []
  end

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
        val fl = true
        val opt = SIM.find (rm,id) (*rm has no WFR constraints*)
        val _ = case opt of
            SOME (r,b,fci) => print ((Int.toString id)^". [rank# "^(Int.toString r)^"]"^
            " - "^(RCs.pprint_ref rc fl)^"\n")
          | NONE => print ((Int.toString id)^".             "^(RCs.pprint_ref rc fl)^"\n")
      in
        ()
      end
    ) () cm

  fun make_initial_solution sri uninst_rqs tm =
    let
      val s = Sol.empty ()
      val om = #orig sri
      fun addrv envir (rf,flag) = case (rf,flag) of
          ((_, RF.RQconst _),_) => ()
        | ((_, RF.RQvar (k, RF.RTop)),false) => if not (Sol.mem s k) 
            then Sol.replace s k [] else ()
        | ((_, RF.RQvar (k, _)),_) => 
          let
            val _ = print "init sol RQvar\n"
            val inst_rqs = instantiate_in_environment envir uninst_rqs
          in
            Sol.replace s k inst_rqs
          end
    in
      (SIM.foldli (fn(id,c,_)=> case c of
          SubRef (rel_env,r1,r2,_) => ()(*addrv rel_env (r1,false); 
            rel_env addrv (r2,true)*)
        | WFRef ((env,renv,g),r,_) => 
          let
            val (lc {lc_cstr=c, ...}) = SIM.find_crash (om,id)
            val f = case c of WFRFrame (_,f) => f | _ => fail "Unexpected Frame\n"
            val envir = (env,renv,g,tm,f)
          in
            addrv envir (r,true)
          end) () (#cnst sri));
      s
    end

  val spc = "        "

  fun pprint_sol s = Sol.foldi 
    (fn (v,inst_qs,str) => str^(Var.toString v)^" -> "^
      "["^(String.concatWith ((List.map(inst_qs,RQ.pprint)),",\n"^spc))^"]\n") "" s

   fun push_worklist sri w cs = List.foldl(cs,w,
      (fn(c,w)=>
      let
        val id = get_ref_id c
        val 
      in
      end
      ))
      (fun w c -> 
        let id = get_ref_id c in
        let _ = C.cprintf C.ol_solve "@[Pushing@ %d@\n@]" id in 
        if Hashtbl.mem sri.pend id then w else 
          let _ = Hashtbl.replace sri.pend id () in
          WH.add (id,get_ref_rank sri c) w)
      w cs 

  fun get_ref_constraints {cnst=ics, ...} = SIM.listitems ics

  fun is_subref_constraint c = case c of SubRef _ => true | _ => false

  fun make_initial_worklist sri =
    let 
      val cs = #yes (List.partition((get_ref_constraints sri),is_subref_constraint)) 
    in
      push_worklist sri WH.empty cs
    end

  fun solve uninst_rqs rcs tm = 
    let
      val rcs = List.map (rcs,RCs.simplify_rfc)
      val sri = make_ref_index (RCs.split rcs) 
      val _  = pprint_sri sri
      val s = make_initial_solution sri uninst_rqs tm
      val _ = print ("** SOL **\n"^(pprint_sol s)^"\n")
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
      val s = solve rqs rcs tm
    in
      ()
    end
end
