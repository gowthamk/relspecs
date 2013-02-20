(* Author: G
 * From Computer Science Department
 * Purdue University *)

signature REL_PREDICATE = 
	sig
    include ATOMS

    (* we are only concerned with variables and integers. Other patterns
       should have suitable bindings in the env *)

  type typedvar = Var.t * Type_desc.type_desc

  datatype relem = 
      RVar of typedvar
    | RInt of int

  datatype rexpr = 
      RRel of Con.t * typedvar (* R(Cons,l); R(Nil,l) *)
    | RSet of relem list (* list of tuples. [1,2]= {(1),(2)} Node(lt,k,v,rt) = {(k,v)} *)
    | RSum of rexpr list
    | RUnion of rexpr list
    | RJoin of Var.t list * rexpr * rexpr
    | RProj of Var.t list * rexpr (* Pi{key,value}R(tree) *)
    | RSel of Predicate.t*rexpr
    | RAgg of Var.t * rexpr

  datatype rbinrel =
      REq
    | RNe
    | RSubset
    | RSuperset

  datatype rel_predicate =
      RFold of Predicate.pexpr * rexpr
    | RAtom of rexpr * rbinrel * rexpr

  datatype rpexpr = 
      RExpr of rexpr
    | PExpr of Predicate.pexpr

  (* Predicate expression *)
  datatype t =
      RTrue
    | RPred of rel_predicate
    | RIff of Predicate.pexpr * t
    | RNot of t
    | RAnd of t * t 
    | ROr of t * t

		(*val pprint_rel: rbinrel -> string
		val pprint: t -> string
		val pprint_rexpr: rexpr -> string*)
		
  val requals : rexpr -> rexpr -> t 
  
  val rnequals : rexpr -> rexpr -> t
  
  val rsub : rexpr -> rexpr -> t	

  val rsup : rexpr -> rexpr -> t	
  
  val rfold : Predicate.pexpr -> rexpr -> t

  val rando : t -> t -> t
  
  val roro : t -> t -> t
  
  val rnoto : t -> t
  
  val riffo: Predicate.pexpr -> t -> t

  val rimply : t -> t -> t
		
  val make_typedvar : Var.t * Type_desc.type_desc -> typedvar

  val make_rvar : typedvar -> relem

  val make_rrel : Con.t * typedvar -> rexpr

  val make_rset : relem list -> rexpr

  val make_runion : rexpr list -> rexpr

  val make_null_rset : unit -> rexpr
(*		val rexpr_length : rexpr -> int*)
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
    | RSum of rexpr list
    | RUnion of rexpr list
    | RJoin of Var.t list * rexpr * rexpr
    | RProj of Var.t list * rexpr (* Pi{key,value}R(tree) *)
    | RSel of Predicate.t*rexpr
    | RAgg of Var.t * rexpr

  datatype rbinrel =
      REq
    | RNe
    | RSubset
    | RSuperset

  datatype rel_predicate =
      RFold of Predicate.pexpr * rexpr
    | RAtom of rexpr * rbinrel * rexpr

  datatype rpexpr = 
      RExpr of rexpr
    | PExpr of Predicate.pexpr

  (* Predicate expression *)
  datatype t =
      RTrue
    | RPred of rel_predicate
    | RIff of Predicate.pexpr * t
    | RNot of t
    | RAnd of t * t 
    | ROr of t * t

  fun requals p q = RPred (RAtom(p, REq, q))

  fun rnequals p q = RPred (RAtom (p, RNe, q))

  fun rsub p q = RPred (RAtom (p, RSubset, q))

  fun rsup p q = RPred (RAtom (p, RSuperset, q))

  fun rando p q = RAnd (p, q)

  fun roro p q = ROr (p, q)

  fun rnoto p = RNot p

  fun riffo p q = RIff (p, q)

  fun rfold p q = case q of
      RAgg _ => RPred (RFold (p, q))
    | _ => (print "rfold over non agg\n"; assertfalse ())

  fun rimply p q = roro (rnoto p) q				

  fun make_typedvar (v) : typedvar = v

  fun make_rvar tv = RVar tv

  fun make_rrel (c,v) = RRel (c,v)

  fun make_rset l = RSet l

  fun make_runion l = RUnion l

  fun make_null_rset () = RSet []
  (*fun rexpr_length rexpr = case rexpr of
      RVar _ => 1 
    | RSet _ => 1
    | RUnion (r1,r2) => (rexpr_length r1) + (rexpr_length r2)   
    | RJoin (attr,r1,r2) => (rexpr_length r1) + (rexpr_length r2) 
    | RProj (_, r) => 1 + rexpr_length r
    | RSel (_, r) => 1 + rexpr_length r
    | RAgg (_, r) => 1 + rexpr_length r*)
end
