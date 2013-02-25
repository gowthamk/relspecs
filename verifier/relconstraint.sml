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
      RSubRef of env * RF.refinement * RF.refinement * bool * int * (Con.t option) * int * (subref_id option) 
    | RWFRef of env * RF.refinement * (subref_id option) 
    
  val hash_fn = HashString.hashString
  
  (**************************************************************)
  (********************** Misc. Constants ***********************)
  (**************************************************************)

  (* return a new constraint indexing *)
  fun fresh_fc_id () = 
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
          RSubRef (rel_env,r1,r2,_,_,_,_,io) =>
          "RSubRef" ^ (pprint_io io) (* ^ ((pprint_env_pred so) env) ^ (P.pprint (guard_predicate () g))*) ^
          " r1 is " ^ (RF.pprint_refinement r1) ^ " r2 is " ^ (RF.pprint_refinement r2) ^ "\n"
        | RWFRef (rel_env,r,io) =>
          "RWFRef" ^ (pprint_io io) (*^ ((pprint_env_pred so) env)*) ^ (RF.pprint_refinement r) ^ "\n"
  
  (* Make labeled constraint 
   * c is a labeled constraint; rfc is a rel frame constraint; 
   *)
  fun make_lc c rfc funflag recordIndex con conrecordIndex = case c of 
      lc c' => (lc {lc_cstr = rfc, lc_orig = RCstr c, lc_id = #lc_id c'}, funflag, recordIndex, con, conrecordIndex)
          
  fun simplylc c = case c of lc c' => c'
        
  
  fun pprint_local_binding (k, v) = ((Var.toString k) ^ " binds to " ^ (RF.pprint v))

  fun pprint_pure_renv renv = 
    RLe.fold (fn x => fn t => fn str => str ^ (pprint_local_binding (x, t)) ^ "\n") renv ""
end
