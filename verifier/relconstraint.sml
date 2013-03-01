structure RelConstraint = 
struct
  open Atoms
  open CoreML

  structure F = Frame
  structure RF = RelFrame
  structure Le = Lightenv
  structure RLe = RelLightenv
  structure P = Predicate
  structure RP = RelPredicate
  structure B = Builtin
  structure RB = RelBuiltin
  structure TP = TheoremProver
  
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

  type env = Le.t * RLe.t * guard_t 
  
  datatype rframe_constraint =
      (* Gamma;guard |-  RF.t => RF.t*)
      SubRFrame of env * RF.t * RF.t
    | WFRFrame of env * RF.t
  
  datatype labeled_constraint = lc of {
    lc_cstr: rframe_constraint,
    lc_orig: origin,
    lc_id: fc_id
  }
  and origin =
      RLoc of (Exp.t option)
    | RAssert of Exp.t 
    | RCstr of labeled_constraint

  
  (* In our solving procedure, we indeed use refinement_constraints 
   * Thus every refinement constraint comes from frame_constraints; attached with subref_id
   * bool value is used as functional subtyping indicator
   *)
  datatype refinement_constraint =
      SubRef of env * RF.refinement * RF.refinement * (subref_id option) 
    | WFRef of env * RF.refinement * (subref_id option) 
    
  val hash_fn = HashString.hashString
  
  (**************************************************************)
  (********************** Misc. Constants ***********************)
  (**************************************************************)

  (* return a new constraint indexing *)
  fun fresh_rfc_id () = 
    let val r = ref 0 
    in fn () => incr r; SOME (!r) end
  
  (* If there is no pending substitution then return true *)
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
          SubRFrame (rel_env,f1,f2) =>
            (* "env is " ^ (pprint_env_pred NONE env) ^ " guard is " ^ (P.pprint(guard_predicate () g)) 
              ^ *) "[S] " ^ (RF.pprint f1) ^ " <: " ^ (RF.pprint f2)
        | WFRFrame (rel_env,f) =>
          (* "env is " ^ (pprint_env_pred NONE env) ^ *)
            "[W] " ^ (RF.pprint f))
  
  fun pprint_io io = 
    case io of
          SOME id => "(" ^ (Int.toString id) ^ ")"
        | NONE    => "()"
  
  fun pprint_ref so refcons =
    case refcons of 
          SubRef (rel_env,r1,r2,io) =>
          "SubRef" ^ (pprint_io io) (* ^ ((pprint_env_pred so) env) ^ (P.pprint (guard_predicate () g))*) ^
          " r1 is " ^ (RF.pprint_refinement r1) ^ " r2 is " ^ (RF.pprint_refinement r2) ^ "\n"
        | WFRef (rel_env,r,io) =>
          "WFRef" ^ (pprint_io io) (*^ ((pprint_env_pred so) env)*) ^ (RF.pprint_refinement r) ^ "\n"
  
  (* Make labeled constraint 
   * c is a labeled constraint; rfc is a rel frame constraint; 
   *)
  fun make_lc c rfc = case c of 
      lc c' => (lc {lc_cstr = rfc, lc_orig = RCstr c, lc_id = #lc_id c'})
          
  fun simplylc c = case c of lc c' => c'
        
  
  fun pprint_local_binding (k, v) = ((Var.toString k) ^ " binds to " ^ (RF.pprint v))

  fun pprint_pure_renv renv = 
    RLe.fold (fn x => fn t => fn str => str ^ (pprint_local_binding (x, t)) ^ "\n") renv ""

  (* Inferred frame should be a subtype of the frame given by users or third party tools *)
  fun mfm (env,renv,g) v rf = 
    if RLe.mem v renv
    then
      let 
        val rf' = RLe.find v renv 
        val rel_env = (env,renv,g)
      in SOME (SubRFrame (rel_env,rf', RF.label_like rf rf')) end
    else NONE 

  fun simplify_rfc rfc = rfc

  fun is_simple_constraint rc = case rc of
      SubRef (_,([],RF.RQvar _),([], RF.RQvar _), _) => true 
    | _ => false

  val qual_test_var = Var.mk_ident "AA"

  val defaultCons = Con.fromString "any"

  val qual_test_expr = RP.make_rrel(defaultCons, 
    RP.make_typedvar(qual_test_var))

  
  fun lequate_rcs rel_env labc rf1 rf2 = [make_lc (lc labc) (SubRFrame(rel_env,rf1,rf2))]

  fun match_and_extend renv (l1,rf1) (l2,rf2) =
    let
      val dummy = RP.make_null_rset()
      val tm = TyconMap.new_tycon_map()
    in
      case(l1,l2) of
        (SOME p, NONE) => (* often case. 
            f1 from real frame. f2 from fresh expr frame (pat is NONE). *)
          (asserti (Pattern.is_simple p,"Fun args should have simple pattern");
          RLe.env_bind renv p rf2 dummy tm)
      | (NONE, SOME p) => 
          (asserti (Pattern.is_simple p,"Fun args should have simple pattern");
          RLe.env_bind renv p rf2 dummy tm)
      | (SOME p1, SOME p2) => if (Pattern.same (p1,p2)) 
        then (asserti (Pattern.is_simple p1 andalso Pattern.is_simple p2,
          "Fun args should have simple pattern");
          RLe.env_bind renv p1 rf2 dummy tm ) (* rare case.
            happens with higher order arguments *)
        else renv
      | _  => renv
    end

  fun split_sub (labc) = case #lc_cstr labc of 
      WFRFrame _ => fail "Unexpected Frame\n"
    | SubRFrame (rel_env,rf1,rf2)  => 
      let
        val rc = #lc_cstr labc
        val (env,renv,g) = rel_env
      in
       case (rf1, rf2) of
          (* l1 and l2 are arg pats *)
          (RF.RFarrow (l1, f1, f1'), RF.RFarrow (l2, f2, f2')) => 
          let 
            val renv' = match_and_extend renv (l1,f1) (l2,f2) 
          in
            (* env' is env extended with precondition (frames for arguments) *)
            ((lequate_rcs rel_env labc f2 f1) @ 
             (lequate_rcs (env,renv',g) labc f1' f2'),
             [])
          end
        | (RF.RFvar _, RF.RFvar _) => ([],[]) 
        | (RF.RFunknown, RF.RFunknown) => ([],[]) 
        | (RF.RFconstr (p1, f1s, r1), RF.RFconstr(p2, f2s,r2)) =>
            (C.flap2 (fn(x,y)=>lequate_rcs rel_env labc x y) f1s f2s,
             [(RCstr (lc labc), SubRef(rel_env,r1,r2,NONE))])
        | (RF.RFrecord (fld1s, r1), RF.RFrecord (fld2s, r2)) =>
            (C.flap2 
               (fn ((f1',_),(f2',_)) => lequate_rcs rel_env labc f1' f2')
               fld1s fld2s, 
             [(RCstr (lc labc), SubRef (rel_env,r1,r2,NONE))])
        | (_,_) => fail ("Can't split: ["^(RF.pprint rf1)^" <: "^(RF.pprint rf2)^"]\n")
       end


  fun split_wf (labc)  = case #lc_cstr labc of
      SubRFrame _ => fail "Unexpected Frame\n" 
    | WFRFrame (rel_env,rf)  =>
      let
        val rc = #lc_cstr labc
        fun make_wff rel_env rf = 
          lc {lc_cstr = WFRFrame (rel_env, rf),
             lc_orig = RCstr (lc labc), lc_id = NONE} 
        val (env,renv,g) = rel_env
        val dummy = RP.make_null_rset()
        val tm = TyconMap.new_tycon_map()
      in
        case rf of
          RF.RFconstr (_,l,r) =>
            (List.map (l,(make_wff rel_env)),
             [(RCstr (lc labc), WFRef ((env,RLe.add qual_test_var rf renv,g), r, NONE))])
        | RF.RFarrow (l, rf, rf') =>
          let
            val renv' = case l of NONE => renv 
              | SOME p => (asserti (Pattern.is_simple p, 
                "Fun args should be a simple pattern");
                RLe.env_bind renv p rf dummy tm)
          in
            ([make_wff rel_env rf, make_wff (env,renv',g) rf'], [])
          end
        | RF.RFrecord (rfs, r) =>
            (List.map (rfs,(fn (rf',_) => make_wff rel_env rf')),
             [(RCstr (lc labc), 
              WFRef ((env,RLe.add qual_test_var rf renv,g), r, NONE))])
        | RF.RFvar _ => ([],[]) 
        | RF.RFunknown => ([],[]) 
      end

(* Here is where we compile down all SubRFrame and WFRFrame constraints 
   to SubRef and WFRef constraints *)
  fun split rcs =
  let
    val _ = asserti (List.forall (rcs,(fn (lc c) => case #lc_id c of 
      SOME _ => true | NONE => false)),
      "Id missing\n")
    in
      C.expand 
        (fn (lc c) => case #lc_cstr c of 
          SubRFrame _ => split_sub c 
        | WFRFrame _ => split_wf c)
        rcs [] 
    end
end
