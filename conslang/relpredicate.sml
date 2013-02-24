(* Author: G
 * From Computer Science Department
 * Purdue University *)

signature REL_PREDICATE = 
	sig
    include ATOMS

    (* we are only concerned with variables and integers. Other patterns
       should have suitable bindings in the env *)

  type typedvar = Var.t

  datatype relem = 
      RVar of typedvar
    | RInt of int

  datatype rexpr = 
      RRel of Con.t * typedvar (* R(Cons,l); R(Nil,l) *)
    | RSet of relem list (* list of tuples. [1,2]= {(1),(2)} Node(lt,k,v,rt) = {(k,v)} *)
    | RUnion of rexpr list
    (*| RJoin of Var.t list * rexpr * rexpr
    | RProj of Var.t list * rexpr (* Pi{key,value}R(tree) *)
    | RSel of Predicate.t*rexpr
    | RAgg of Var.t * rexpr*)

  datatype rbinrel =
      REq
    | RNe
    | RSubset
    | RSuperset

  datatype rel_predicate =
      RAtom of rexpr * rbinrel * rexpr
  (*  | RFold of Predicate.pexpr * rexpr *)

  datatype rpexpr = 
      RExpr of rexpr
    (*| PExpr of Predicate.pexpr*)

  (* Predicate expression *)
  datatype t =
      RTrue
    | RPred of rel_predicate
    (*| RIff of Predicate.pexpr * t*)
    | RNot of t
    | RAnd of t * t 
    | ROr of t * t

		(*val pprint_rel: rbinrel -> string
		val pprint_rexpr: rexpr -> string*)

  val pprint: t -> string

  (* Update some predicate var with another instance of var *)
  val instantiate_named_vars: (string * Var.t) list -> t -> t

  val requals : rexpr -> rexpr -> t 
  
  val rnequals : rexpr -> rexpr -> t
  
  val rsub : rexpr -> rexpr -> t	

  val rsup : rexpr -> rexpr -> t	
  
 (* val rfold : Predicate.pexpr -> rexpr -> t*)

  val rando : t -> t -> t
  
  val roro : t -> t -> t
  
  val rnoto : t -> t
  
  (*val riffo: Predicate.pexpr -> t -> t*)

  val rimply : t -> t -> t
		
  val make_typedvar : Var.t  -> typedvar

  val make_rvar : typedvar -> relem

  val make_rrel : Con.t * typedvar -> rexpr

  val make_rset : relem list -> rexpr

  val make_runion : rexpr list -> rexpr

  val make_dummy_rexpr : unit -> rexpr
		
  val make_null_rset : unit -> rexpr
end
	
structure RelPredicate :REL_PREDICATE =
struct

  open Atoms
  open Common

  type typedvar = Var.t

  datatype relem = 
      RVar of typedvar
    | RInt of int

  datatype rexpr = 
      RRel of Con.t * typedvar (* R(Cons,l); R(Nil,l) *)
    | RSet of relem list (* list of tuples. [1,2]= {(1),(2)} Node(lt,k,v,rt) = {(k,v)} *)
    | RUnion of rexpr list
    (*| RJoin of Var.t list * rexpr * rexpr
    | RProj of Var.t list * rexpr (* Pi{key,value}R(tree) *)
    | RSel of Predicate.t*rexpr
    | RAgg of Var.t * rexpr*)

  datatype rbinrel =
      REq
    | RNe
    | RSubset
    | RSuperset

  datatype rel_predicate =
      RAtom of rexpr * rbinrel * rexpr
  (*  | RFold of Predicate.pexpr * rexpr *)

  datatype rpexpr = 
      RExpr of rexpr
    (*| PExpr of Predicate.pexpr*)

  (* Predicate expression *)
  datatype t =
      RTrue
    | RPred of rel_predicate
    (*| RIff of Predicate.pexpr * t*)
    | RNot of t
    | RAnd of t * t 
    | ROr of t * t

  fun pprint t = "RP.pprint"

  fun make_dummy_rexpr () =
  let
    val dummy_var = Var.mk_ident "dummy"
    val any_cons = Con.fromString "any"
  in
    RRel (any_cons,dummy_var)
  end

  fun requals p q = RPred (RAtom(p, REq, q))

  fun rnequals p q = RPred (RAtom (p, RNe, q))

  fun rsub p q = RPred (RAtom (p, RSubset, q))

  fun rsup p q = RPred (RAtom (p, RSuperset, q))

  fun rando p q = RAnd (p, q)

  fun roro p q = ROr (p, q)

  fun rnoto p = RNot p

  (*fun riffo p q = RIff (p, q)*)

  (*fun rfold p q = case q of
      RAgg _ => RPred (RFold (p, q))
    | _ => (print "rfold over non agg\n"; assertfalse ())*)

  fun rimply p q = roro (rnoto p) q				

  fun make_typedvar (v) : typedvar = v

  fun make_rvar tv = RVar tv

  fun make_rrel (c,v) = RRel (c,v)

  fun make_rset l = RSet l

  fun make_runion l = RUnion l

  fun make_null_rset () = RSet []

  fun rexpr_map_vars f rexp =
    let val rec map_rec = fn
        RRel (c,v) => RRel (c,f v)
      | RSet l =>
          RSet (List.map(l,
            (fn x => case x of
                RVar v => RVar (f v)
              | _ => x)))
      | RUnion l => RUnion (List.map(l,map_rec))
      | e => e
    in map_rec rexp end

  fun rpred_map_vars f rp = case rp of
    RAtom (re1,br,re2) => RAtom ((rexpr_map_vars f re1),br,(rexpr_map_vars f re2))
  | _ => fail "unexpected rpred\n"
  
  fun map_vars f pred =
    let val rec map_rec = fn
        RTrue =>
          RTrue
      | RPred rp => RPred (rpred_map_vars f rp)
      | RNot p =>
          RNot (map_rec p)
      | RAnd (p, q) =>
          RAnd (map_rec p, map_rec q)
      | ROr (p, q) =>
          ROr (map_rec p, map_rec q)
    in map_rec pred end	  
  
  fun instantiate_named_vars subs rpred =
    map_vars (fn y => (Common.assoc1 (Var.toString y) subs)) rpred
end
