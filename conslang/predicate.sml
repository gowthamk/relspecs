(* Author: He Zhu
 * From Computer Science Department
 * Purdue University *)

signature PREDICATE = 
	sig
		include ATOMS
		datatype binop = 
		    Plus
		  | Minus
		  | Times
		  | Div
		  | Mod
		
		datatype binrel =
		    Eq
		  | Ne
		  | Gt
		  | Ge
		  | Lt
		  | Le 
		
		(* Simple expression*)
		datatype pexpr =
		    PInt of int 
		  | PVar of Var.t
		  | FunApp of string * pexpr list  
		  | Binop of pexpr * binop * pexpr
		  | Field of string * pexpr
		  | Proj of int * pexpr
		  | Tuplelist of pexpr list
		
		(* Predicate expression *)
		datatype t =
		    True
		  | Atom of pexpr * binrel * pexpr 
		  | Iff of pexpr * t
		  | Not of t
		  | And of t * t 
		  | Or of t * t
		  		  		  		
		val pprint_rel: binrel -> string
		val pprint: t -> string
		val pprint_pexpr: pexpr -> string
		
		val compact_pprint_pexpr : pexpr -> string
		
		val big_and: t list -> t
		val big_or: t list -> t
		val int_true: pexpr
		val int_false: pexpr
		val expand_iff: t -> t
		
		(* Replace one predicate var with an pending substitution *)
		val subst: pexpr -> Var.t -> t -> t
		
		val subst2 : pexpr -> pexpr -> t -> t
		
		(* pending substitution works in the predicate *)
		val apply_substs: (Var.t * pexpr) list -> t -> t
	
		val exp_vars : pexpr -> Var.t list
		
		val vars: t -> Var.t list
		
		(* Update some predicate var with another instance of var *)
		val instantiate_named_vars: (string * Var.t) list -> t -> t
		
		val transl_pattern_pred : PATQualifier.t -> (Var.t * Var.t * t) list
		
		val logic_equals_pexp : pexpr -> pexpr -> bool
		
		val logic_equals : (t * t) -> bool
		
		val equals : pexpr -> pexpr -> t 
		
		val nequals : pexpr -> pexpr -> t
		
		val ge : pexpr -> pexpr -> t
		
		val g : pexpr -> pexpr -> t
		
		val le : pexpr -> pexpr -> t
		
		val l : pexpr -> pexpr -> t
		
		val ando : t -> t -> t
		
		val oro : t -> t -> t
		
		val noto : t -> t
		
		val iffo : pexpr -> t -> t
		
		val pluso  : pexpr -> pexpr -> pexpr
		
		val mulo : pexpr -> pexpr -> pexpr
		
		val divo : pexpr -> pexpr -> pexpr
		
		val minuso : pexpr -> pexpr -> pexpr   
		
		val modo : pexpr -> pexpr-> pexpr   
		
		val imply : t -> t -> t
		
		val envgen_preds : t -> Var.t list -> t list
		
		val andPredicateList : t -> t list
		
		val size : t -> int
		
		val addFunApp : t -> t
		
		val getAddFunApp : t -> t list
		
		val containVar : Var.t -> t -> bool
		
		val containVars : Var.t list -> t -> bool
		
		val containPexpr : pexpr -> t -> (bool * (pexpr option))
		
		val simplify_predpexpr : pexpr -> pexpr
		
		val simplify_pred : t -> t
		
		
		
		val map_vars : (Var.t -> pexpr) -> t -> t
		
		val getFunversion : t -> Var.t list -> (pexpr option)
		
		val compressHOFunTermToVar : t -> (t * (Var.t * pexpr) list)
		
		val hasHovConstraint : t -> bool
		
		val last_Not_Or : t -> t		
	
		val share : t -> t -> bool
		
		val containFunversion : t -> bool
		
		val simplify_predicate : t -> (t*bool)
		
		val pexpr_length : pexpr -> int
	end
	
structure Predicate : PREDICATE =
	struct

		open Atoms
		open Common
		
		open PATQualifier
		open PATPredicate
		
		datatype binop =
		    Plus
		  | Minus
		  | Times
		  | Div
		  | Mod
		
		datatype binrel =
		    Eq
		  | Ne
		  | Gt
		  | Ge
		  | Lt
		  | Le 
		
		(* Simple expression*)
		datatype pexpr =
		    PInt of int 
		  | PVar of Var.t
		  | FunApp of string * pexpr list  
		  | Binop of pexpr * binop * pexpr
		  | Field of string * pexpr
		  | Proj of int * pexpr
		  | Tuplelist of pexpr list
		
		(* Predicate expression*)
		datatype t =
		    True
		  | Atom of pexpr * binrel * pexpr 
		  | Iff of pexpr * t
		  | Not of t
		  | And of t * t 
		  | Or of t * t
		  
		fun lflap es =
			case es of
				  s :: [] => List.map (s, (fn c => [c]))
		    	| s :: es => Common.flap (fn c => List.map ((lflap es), (fn d => c :: d))) s
		    	| [] => []
		
		fun tflap3 (e1, e2, e3) f = Common.flap (fn c => Common.flap (fn d => List.map (e3, (fn e => f c d e))) e2) e1
		
		fun tflap2 (e1, e2) f = Common.flap (fn c => List.map (e2, (fn d => f c d))) e1
		
		fun translateoprs oprs = 
			List.map (oprs, (fn opr => case opr of
				  PATPredicate.Plus => Plus
				| PATPredicate.Minus => Minus
				| PATPredicate.Times => Times
				| PATPredicate.Div => Div
			))
				
		fun translaterels rels = 
			List.map (rels, (fn rel => case rel of
				  PATPredicate.Eq => Eq
				| PATPredicate.Ne => Ne
				| PATPredicate.Gt => Gt
				| PATPredicate.Ge => Ge
				| PATPredicate.Lt => Lt
				| PATPredicate.Le => Le
			))
		
		fun gen_preds p =
			let fun gen_expr_rec pe =
			    case pe of
			        PPInt (ns) =>
			          List.map (ns, (fn c => PInt (c)))  
			      | PATPredicate.PVar (ps) =>
			          List.map (ps, (fn c => PVar (Var.fromString c)))
			      | PFunApp (f, es) =>
			          let 
			              val ess = List.map (es, gen_expr_rec) 
			          in
			            List.map ((lflap ess), (fn e => FunApp (f, e)))
			          end
			      | PBinop (e1, ops, e2) =>
			          let val e1s = gen_expr_rec e1
			              val e2s = gen_expr_rec e2
			              val ops' = translateoprs ops
			          in
			          	  tflap3 (e1s, ops', e2s) (fn c => fn d => fn e => Binop (c, d, e))
			          end
			      | PField (f, e1) =>
			          let val e1s = gen_expr_rec e1 
			          in List.map (e1s, (fn e => Field(f, e))) end
			      | PProj (n, e1) =>
			          let val e1s = gen_expr_rec e1 
			          in List.map (e1s, (fn e => Proj(n, e))) end
			in
				let fun gen_pred_rec pd =
				    case pd of
				        PTrue => [True] 
				      | PNot (p) => List.map ((gen_pred_rec p), (fn c => Not (c))) 
				      | POr (p1, p2) =>
				      		let val p1s = gen_pred_rec p1
				      			val p2s = gen_pred_rec p2
							in tflap2 (p1s, p2s) (fn c => fn d => Or (c, d)) end
				      | PAnd (p1, p2) =>
				      		let val p1s = gen_pred_rec p1
				      			val p2s = gen_pred_rec p2 
				      		in tflap2 (p1s, p2s) (fn c => fn d => And (c, d)) end
				      | PAtom (e1, rels, e2) =>
				      		let val e1s = gen_expr_rec e1
				      			val e2s = gen_expr_rec e2 
				      			val rels' = translaterels rels
				      		in tflap3 (e1s, rels', e2s) (fn c => fn d => fn e => Atom (c, d, e)) end
				      | PIff (e1, p1) =>
				      		let val e1s = gen_expr_rec e1
				      			val p1s = gen_pred_rec p1 
				      		in tflap2 (e1s, p1s) (fn c => fn d => Iff (c, d)) end
				in gen_pred_rec p end
			end
			
		fun transl_pattern_pred ((name, valu, pred)) =
			let 
				val num = ref 0
				fun fresh name = Var.fromString (Common.incr num; name ^ (Int.toString (!num)))
				val preds = gen_preds pred 
			in
				List.map (preds, (fn p => (fresh name, Var.fromString valu, p)))
			end
		
		val pprint_rel = fn
			Eq => "="
			| Ne => "!="
		  	| Gt => ">"
		  	| Ge => ">="
		  	| Lt => "<"
		  	| Le => "<="
		  
		val pprint_opstr = fn
	    	Plus => "+"
	    	| Minus => "-"
	        | Times => "*"
			| Div => "/"
			| Mod => "|"
		
		val rec print_list = fn pr => fn sep => fn li =>
			case li of
		    	  nil => ""
				| [a] => pr a
				| a :: l => ((pr a) ^ sep ^ (print_list pr sep l))
				
		(* Print simple expression *)
		val rec pprint_pexpr = fn 
			PInt n =>
		      if n < 0 then (Int.toString (~n))
		      else (Int.toString(n))
		  | PVar x => (Var.toString x)
		  | FunApp (f, pexp) =>
		      (f ^ " " ^ (print_list pprint_pexpr " " pexp))
		  | Binop (p, opr, q) =>
		      let val opstr = case opr of
		          Plus => "+"
		        | Minus => "-"
		        | Times => "*"
				| Div => "/"
				| Mod => "|"
		      in ("(" ^ (pprint_pexpr p) ^ (opstr) ^ (pprint_pexpr q) ^ ")") end
		  | Field (f, pexp) =>
		      ((pprint_pexpr pexp) ^ "." ^ f)
		  | Proj (n, pexp) =>
		      ((pprint_pexpr pexp) ^ "." ^ (Int.toString n))
		  | Tuplelist pexprlist => "The following is just an intermediate repr due to sml dialect " ^ (print_list pprint_pexpr " " pexprlist)
		
		(* Print predicate expression *)
		val rec pprint = fn
		    True => "true"
		  | Atom (p, rel, q) => ("(" ^ (pprint_pexpr p) ^ (pprint_rel rel) ^ (pprint_pexpr q)^ ")")
		  | Iff (px, q) => ((pprint_pexpr px) ^ "<=>" ^ (pprint q))
		  | Not p => ("not (" ^ (pprint p) ^ ")")
		  | And (p, q) => ("(" ^ (flatten_conjuncts p) ^ " and " ^ (flatten_conjuncts q) ^ ")")
		  | Or (p, q) => ("(" ^ (flatten_disjuncts p) ^ " or " ^ (flatten_disjuncts q) ^ ")")
		and flatten_conjuncts = fn
		    And (And (p1, p2), And (q1, q2)) =>
		        ((flatten_conjuncts p1) ^ " and " ^ (flatten_conjuncts p2) ^
		        (flatten_conjuncts q1) ^ " and " ^ (flatten_conjuncts q2))
		  | And (And (p1, p2), q) =>
		  		((pprint q) ^ " and " ^ (flatten_conjuncts p1) ^ " and " ^ (flatten_conjuncts p2))
		  | And (q, And (p1, p2)) =>
		        ((pprint q) ^ " and " ^ (flatten_conjuncts p1) ^ " and " ^ (flatten_conjuncts p2))
		  | p => pprint p
		and flatten_disjuncts = fn
		    Or (Or (p1, p2), Or (q1, q2)) =>
		        ((flatten_disjuncts p1) ^ " or " ^ (flatten_disjuncts p2) ^
		        (flatten_disjuncts q1) ^ " or " ^ (flatten_disjuncts q2))
		  | Or (Or (p1, p2), q) =>
		  		((pprint q) ^ "or" ^ (flatten_disjuncts p1) ^ " or " ^ (flatten_disjuncts p2))
		  | Or (q, Or (p1, p2)) =>
		        ((pprint q) ^ "or" ^ (flatten_disjuncts p1) ^ "or" ^ (flatten_disjuncts p2))
		  | p => pprint p
		         
		        
		
		(* Print simple expression *)
		val rec compact_pprint_pexpr = fn 
			PInt n =>
		      if n < 0 then (Int.toString (~n))
		      else (Int.toString(n))
		  | PVar x => (Var.toString x)
		  | FunApp (f, pexp) =>
		      (f ^ (print_list compact_pprint_pexpr "" pexp))
		  | Binop (p, opr, q) =>
		      let val opstr = case opr of
		          Plus => "+"
		        | Minus => "-"
		        | Times => "*"
				| Div => "/"
				| Mod => "|"
		      in ((compact_pprint_pexpr p) ^ (opstr) ^ (compact_pprint_pexpr q)) end
		  | Field (f, pexp) =>
		      ((compact_pprint_pexpr pexp) ^ "." ^ f)
		  | Proj (n, pexp) =>
		      ((compact_pprint_pexpr pexp) ^ "." ^ (Int.toString n))
		  | Tuplelist pexprlist => "The following is just an intermediate repr due to sml dialect " ^ (print_list compact_pprint_pexpr " " pexprlist)
		
		(* Print predicate expression *)
		val rec compact_pprint = fn
		    True => "true"
		  | Atom (p, rel, q) => ((compact_pprint_pexpr p) ^ (pprint_rel rel) ^ (compact_pprint_pexpr q))
		  | Iff (px, q) => ((compact_pprint_pexpr px) ^ "<=>" ^ (compact_pprint q))
		  | Not p => ("not" ^ (compact_pprint p))
		  | And (p, q) => ((compact_flatten_conjuncts p) ^ "and" ^ (compact_flatten_conjuncts q))
		  | Or (p, q) => ((compact_flatten_disjuncts p) ^ "or" ^ (compact_flatten_disjuncts q))
		and compact_flatten_conjuncts = fn
		    And (And (p1, p2), And (q1, q2)) =>
		        ((compact_flatten_conjuncts p1) ^ "and" ^ (compact_flatten_conjuncts p2) ^
		        (compact_flatten_conjuncts q1) ^ "and" ^ (compact_flatten_conjuncts q2))
		  | And (And (p1, p2), q) =>
		  		((compact_pprint q) ^ "and" ^ (compact_flatten_conjuncts p1) ^ "and" ^ (compact_flatten_conjuncts p2))
		  | And (q, And (p1, p2)) =>
		        ((compact_pprint q) ^ "and" ^ (compact_flatten_conjuncts p1) ^ "and" ^ (compact_flatten_conjuncts p2))
		  | p => compact_pprint p
		and compact_flatten_disjuncts = fn
		    Or (Or (p1, p2), Or (q1, q2)) =>
		        ((compact_flatten_disjuncts p1) ^ "or" ^ (compact_flatten_disjuncts p2) ^
		        (compact_flatten_disjuncts q1) ^ "or" ^ (compact_flatten_disjuncts q2))
		  | Or (Or (p1, p2), q) =>
		  		((compact_pprint q) ^ "or" ^ (compact_flatten_disjuncts p1) ^ "or" ^ (compact_flatten_disjuncts p2))
		  | Or (q, Or (p1, p2)) =>
		        ((pprint q) ^ "or" ^ (compact_flatten_disjuncts p1) ^ "or" ^ (compact_flatten_disjuncts p2))
		  | p => compact_pprint p
		
		(* This hard-coded implementation may be error-prone *)
		val (int_true, int_false) = (PInt 1, PInt 0)
		
		val expand_iff = fn
		    (Iff (px, q)) => Or (And (Atom (px, Eq, int_true), q), And (Atom(px, Eq, int_false), Not q))
		  | _ => assertfalse ()
		
		val big_and = fn
		    c :: cs => List.fold (cs, c, And)
		  | [] => True
		
		val big_or = fn
		    c :: cs => List.fold (cs, c, Or)
		  | [] => Not True
		
		val rec pexp_map_vars = fn f => fn pexp =>
		  let val rec map_rec = fn
		      PVar x => f x
		    | FunApp (fu, e) =>
		        FunApp (fu, List.map (e, map_rec))
		    | Binop (e1, opr, e2) =>
		        Binop (map_rec e1, opr, map_rec e2)
		    | Field (f, pexp) =>
		        Field (f, map_rec pexp)
		    | Proj (n, pexp) =>
		        Proj (n, map_rec pexp)
		    | e => e
		  in map_rec pexp end
		
		val rec map_vars = fn f => fn pred =>
		  let val rec map_rec = fn
		      True =>
		        True
		    | Atom (e1, rel, e2) =>
		        Atom (pexp_map_vars f e1, rel, pexp_map_vars f e2)
		    | Iff (px, q) => Iff (pexp_map_vars f px, map_rec q)
		    | Not p =>
		        Not (map_rec p)
		    | And (p, q) =>
		        And (map_rec p, map_rec q)
		    | Or (p, q) =>
		        Or (map_rec p, map_rec q)
		  in map_rec pred end	  
		  
		fun logic_equals_pexp pexp1 pexp2 = 
			case (pexp1, pexp2) of
				  (PInt x, PInt x') => (x = x')	
				| (PVar x, PVar x') => Var.logic_equals (x, x')
				| (FunApp (fu, e), FunApp (fu', e')) => (String.compare (fu, fu') = EQUAL)
															andalso (List.forall2 (e, e', (fn (p, p') => logic_equals_pexp p p')))
          (* but, all binops are associative?? *)
				| (Binop (e1, opr, e2), Binop (e1', opr', e2')) =>
						if(String.compare (pprint_opstr opr, pprint_opstr opr') = EQUAL)
						then
							(logic_equals_pexp e1 e1') andalso (logic_equals_pexp e2 e2')
						else false
				| (Field (f, pexp), Field (f', pexp')) => 
					(String.compare (f, f') = EQUAL) andalso (logic_equals_pexp pexp pexp')
          (* simplify_pexpr called previously?? *)
				| (Proj (n, pexp), Proj (n', pexp')) =>
					(n = n') andalso (logic_equals_pexp pexp pexp')
				| (Tuplelist pexprlist, Tuplelist pexprlist') => 
					List.forall2 (pexprlist, pexprlist', (fn (p, p') => logic_equals_pexp p p'))
				| _ => false 

		
		fun logic_equals (p1, p2) =
			case (p1, p2) of 
				  (True, True) => true
				| (Atom (e1, rel, e2), Atom (e1', rel', e2')) =>
					if (String.compare (pprint_rel rel, pprint_rel rel') = EQUAL) 
					then
						(logic_equals_pexp e1 e1') andalso (logic_equals_pexp e2 e2')
					else false
				| (Iff (px, q), Iff (px', q')) => (logic_equals_pexp px px') andalso (logic_equals (q, q'))
				| (Not p, Not p') => (logic_equals (p, p'))
				| (And (p, q), And (p', q')) => (logic_equals (p, p')) andalso (logic_equals (q, q'))
				| (Or (p, q), Or (p', q')) => (logic_equals (p, p')) andalso (logic_equals (q, q'))
				| _ => false
		
		
		val rec simplify_predpexpr = fn pexp =>
		  let val rec simplify_predpexpr_rec = fn
		      PVar x => PVar x
		    | FunApp (fu, e) =>
		        FunApp (fu, List.map (e, simplify_predpexpr_rec))
		    | Binop (e1, opr, e2) =>
		        Binop (simplify_predpexpr_rec e1, opr, simplify_predpexpr_rec e2)
		    | Field (f, pexp) =>
		        Field (f, simplify_predpexpr_rec pexp)
		    | Proj (n, Tuplelist li) => List.nth (li, n-1)
		    | Proj (n, pexp) =>
		        Proj (n, simplify_predpexpr_rec pexp)
		    | e => e
		  in simplify_predpexpr_rec pexp end
		  
		val rec simplify_pred = fn pred =>
			let val rec simplify_pred_rec = fn
			      True => True
			    | Atom (e1, rel, e2) =>
			        Atom (simplify_predpexpr e1, rel, simplify_predpexpr e2)
			    | Iff (px, q) => Iff (simplify_predpexpr px, simplify_pred_rec q)
			    | Not p =>
			        Not (simplify_pred_rec p)
			    | And (p, q) =>
			        And (simplify_pred_rec p, simplify_pred_rec q)
			    | Or (p, q) =>
			        Or (simplify_pred_rec p, simplify_pred_rec q)
		  	in simplify_pred_rec pred end
		
		val subst = fn v => fn x => fn pred =>
			map_vars (fn y => if (Var.logic_equals (x, y)) then v else PVar y) pred
			
		fun subst2pexpr ev ex e = 
			if (logic_equals_pexp ex e) then ev
			else
				case e of 
					PVar x => e
					| FunApp (fu, es) => FunApp (fu, List.map (es, subst2pexpr ev ex))
					| Binop (e1, opr, e2) => Binop (subst2pexpr ev ex e1, opr, subst2pexpr ev ex e2)
					| Field (f, pexp) => Field (f, subst2pexpr ev ex pexp)
					| Proj (n, Tuplelist li) => e
					| Proj (n, pexp) => Proj (n, subst2pexpr ev ex pexp)
					| e => e
			
		fun subst2 ev ex pred = case pred of
			True => True
		    | Atom (e1, rel, e2) =>
		        Atom (subst2pexpr ev ex e1, rel, subst2pexpr ev ex e2)
		    | Iff (px, q) => Iff (subst2pexpr ev ex px, subst2 ev ex q)
		    | Not p =>
		        Not (subst2 ev ex p)
		    | And (p, q) =>
		        And (subst2 ev ex p, subst2 ev ex q)
		    | Or (p, q) =>
		        Or (subst2 ev ex p, subst2 ev ex q)	
		        
		fun containPexprPexpr pexpr e = 
			if (logic_equals_pexp e pexpr) then 
				case e of 
					Proj (_, Field _) => (true, SOME e)
					| _ => (true, NONE)
			else
				case e of 
					PVar x => (false, NONE)
					| FunApp (fu, es) => 
						List.fold (es, (false, NONE), fn (e, (b1, px1)) => 
							let val (b2, px2) = containPexprPexpr pexpr e
							in
								case (px1, px2) of 
								(SOME px1, SOME px2) => (true, SOME px1)
								| (SOME px1, NONE) => (true, SOME px1)
								| (NONE, SOME px2) => (true, SOME px2)
								| _ => ((b1 orelse b2), NONE) 
							end
						)
					| Binop (e1, opr, e2) => 
						let val (b1, px1) = (containPexprPexpr pexpr e1)
							val (b2, px2) = (containPexprPexpr pexpr e2)
						in
							case (px1, px2) of 
								(SOME px1, SOME px2) => (true, SOME px1)
								| (SOME px1, NONE) => (true, SOME px1)
								| (NONE, SOME px2) => (true, SOME px2)
								| _ => ((b1 orelse b2), NONE) 
						end
					| Field (f, pexp) => (containPexprPexpr pexpr pexp)
					| Proj (n, Tuplelist li) => (false, NONE)
					| Proj (n, pexp) => (containPexprPexpr pexpr pexp)
					| e => (false, NONE)
		        
		fun containPexpr pexpr pred = case pred of 
			True => (false, NONE)
			| Atom (e1, rel, e2) => 
				let val (b1, px1) = (containPexprPexpr pexpr e1)
					val (b2, px2) = (containPexprPexpr pexpr e2)
				in
					case (px1, px2) of 
						(SOME px1, SOME px2) => (true, SOME px1)
						| (SOME px1, NONE) => (true, SOME px1)
						| (NONE, SOME px2) => (true, SOME px2)
						| _ => ((b1 orelse b2), NONE) 
				end
			| Iff (px, q) => 
				let val (b1, px1) = (containPexprPexpr pexpr px)
					val (b2, px2) = (containPexpr pexpr q)
				in
					case (px1, px2) of 
						(SOME px1, SOME px2) => (true, SOME px1)
						| (SOME px1, NONE) => (true, SOME px1)
						| (NONE, SOME px2) => (true, SOME px2)
						| _ => ((b1 orelse b2), NONE) 
				end
			| Not p => containPexpr pexpr p
			| And (p, q) =>
				let val (b1, px1) = (containPexpr pexpr p)
					val (b2, px2) = (containPexpr pexpr q)
				in
					case (px1, px2) of 
						(SOME px1, SOME px2) => (true, SOME px1)
						| (SOME px1, NONE) => (true, SOME px1)
						| (NONE, SOME px2) => (true, SOME px2)
						| _ => ((b1 orelse b2), NONE) 
				end
			| Or (p, q) => 
				let val (b1, px1) = (containPexpr pexpr p)
					val (b2, px2) = (containPexpr pexpr q)
				in
					case (px1, px2) of 
						(SOME px1, SOME px2) => (true, SOME px1)
						| (SOME px1, NONE) => (true, SOME px1)
						| (NONE, SOME px2) => (true, SOME px2)
						| _ => ((b1 orelse b2), NONE) 
				end
		
		(* We do substitution here to perform substitution in pred. Note subs are map with x (string now) 
		   as index mapped to an expression e *)
		(* (Var.t * pexpr) list -> t -> t *)
		val apply_substs = fn subs => fn pred =>
			let 
				val substitute = fn ((x, e), p) => subst e x p 
			in 
				simplify_pred (List.fold (subs, pred, substitute))
			end
		
		(* (string * Var.t) list -> t -> t *)
    (* forall vars in pred, if var.toString is there in list, 
       substitue it with replacement var.
       else raise Common,not_found *)
		val instantiate_named_vars = fn subs => fn pred =>
			map_vars (fn y => PVar (Common.assoc1 (Var.toString y) subs)) pred
					
		val exp_vars_unexp = fn
		    PInt _ => ([], [])
		  | PVar x => ([], [x])
		  | Binop (e1, _, e2) => ([e1, e2], [])
		  | FunApp (_, es) => (es, [])
		  | Field (_, e) => ([e], [])
		  | Proj (_, e) => ([e], [])
		  | _ => ([], [])
		
		val exp_vars = fn e =>
		  expand exp_vars_unexp [e] []
		
		val var_unexp = fn
		    True => ([], [])
		  | Atom (e1, _, e2) => ([], exp_vars e1 @ exp_vars e2)
		  | Iff (e, q) => ([q], exp_vars e)
		  | Not p => ([p], [])
		  | And (p, q) => ([p, q], []) 
		  | Or (p, q) => ([p, q], [])
		
		(* Extract all vars from an predicate expression *)
		val vars = fn e => expand var_unexp [e] []
		

		fun equals p q = Atom(p, Eq, q)
		
		fun nequals p q = Atom (p, Ne, q)
		
		fun ge p q = Atom (p, Ge, q)
		
		fun g p q = Atom (p, Gt, q)
		
		fun le p q = Atom (p, Le, q)
		
		fun l p q = Atom (p, Lt, q)
		
		fun ando p q = And (p, q)
		
		fun oro p q = Or (p, q)
		
		fun noto p = Not p
		
		fun iffo p q = Iff (p, q)
		
		fun pluso p q = Binop (p, Plus, q)
		
		fun mulo p q = Binop (p, Times, q)
		
		fun divo p q = Binop (p, Div, q)
		
		fun minuso p q = Binop (p, Minus, q)         
		
		fun modo p q = Binop (p, Mod, q)
		
		fun imply p q = oro (noto p) q				
				
		fun envgen_preds p vs =
			let fun gen_expr_rec pe =
			    case pe of
			        PInt n => [PInt n]
			      | PVar v => if (String.compare ((Var.toString v), "~A") = EQUAL) then 
			      				List.map (vs, (fn c => PVar c))
							  else [PVar v]
			      | FunApp (f, es) =>
			          let 
			              val ess = List.map (es, gen_expr_rec) 
			          in
			            List.map ((lflap ess), (fn e => FunApp (f, e)))
			          end
			      | Binop (e1, ops, e2) =>
			          let val e1s = gen_expr_rec e1
			              val e2s = gen_expr_rec e2
			          in
			          	  tflap2 (e1s, e2s) (fn c => fn d => Binop (c, ops, d))
			          end
			      | Field (f, e1) =>
			          let val e1s = gen_expr_rec e1 
			          in List.map (e1s, (fn e => Field(f, e))) end
			      | Proj (n, e1) =>
			          let val e1s = gen_expr_rec e1 
			          in List.map (e1s, (fn e => Proj(n, e))) end
			      | _ => (print "No tuplelist instantiating qual stage"; assertfalse())
			in
				let fun gen_pred_rec pd =
				    case pd of
				        True => [True] 
				      | Not (p) => List.map ((gen_pred_rec p), (fn c => Not (c))) 
				      | Or (p1, p2) =>
				      		let val p1s = gen_pred_rec p1
				      			val p2s = gen_pred_rec p2
							in tflap2 (p1s, p2s) (fn c => fn d => Or (c, d)) end
				      | And (p1, p2) =>
				      		let val p1s = gen_pred_rec p1
				      			val p2s = gen_pred_rec p2 
				      		in tflap2 (p1s, p2s) (fn c => fn d => And (c, d)) end
				      | Atom (e1, rels, e2) =>
				      		let val e1s = gen_expr_rec e1
				      			val e2s = gen_expr_rec e2 
				      		in tflap2 (e1s, e2s) (fn c => fn d => Atom (c, rels, d)) end
				      | Iff (e1, p1) =>
				      		let val e1s = gen_expr_rec e1
				      			val p1s = gen_pred_rec p1 
				      		in tflap2 (e1s, p1s) (fn c => fn d => Iff (c, d)) end
				in gen_pred_rec p end
			end
			
		fun andPredicateList p =
			case p of 
				  True => [True]
				| Not p => [Not p]
				| Or (p1, p2) => [p]
				| And (p1, p2) => (andPredicateList p1) @ (andPredicateList p2)
				| Atom (e1, rel, e2) => [p]
				| Iff (e, p') => [p]
				
		fun size p = 
			List.length (andPredicateList p)
				
		(*
		 * Wrong implementation. But works for most of the cases. Not very much need to elevate it the correct level.
		 *)
		fun getAddFunApp p = 
			let val funapps = ref []
				fun addFunAppSuffix' pexpr = 
					case pexpr of
						  PVar x => ()
					    | FunApp (fu, e) => List.push (funapps, equals (PVar (Var.fromString ((compact_pprint_pexpr pexpr)^"_"))) pexpr)
					    | Binop (e1, opr, e2) => (addFunAppSuffix' e1; addFunAppSuffix' e2)
					    | Field (f, pexp) => ()
					    | Proj (n, pexp) => ()
					    | e => ()
				fun addFunAppSuffix p = 
					case p of 
						  True => ()
						| Not p => addFunAppSuffix p
						| Or (p1, p2) => (addFunAppSuffix p1; addFunAppSuffix p2)
						| And (p1, p2) => (addFunAppSuffix p1; addFunAppSuffix p2)
						| Atom (e1, rel, e2) => (addFunAppSuffix' e1; addFunAppSuffix' e2) 
						| Iff (e, p') => (addFunAppSuffix' e; addFunAppSuffix p')
				val _ = addFunAppSuffix p
			in (!funapps) end			
			 
		 
		fun addFunApp p = 
			let val funapps = getAddFunApp p
				val li = p :: funapps
			in
				big_and li
			end
			
		fun containVar var pred = 
			let val vars = vars pred
			in
				List.exists (vars, fn v => Var.logic_equals (v, var))
			end
			
		fun containVars varlist pred = 
			let val vars = vars pred
			in
				List.exists (vars, fn v => (List.exists (varlist, fn v' => Var.logic_equals (v, v'))))
			end
		
		fun varIndexGreat pe1 pe2 = 
			let val var1 = List.first (exp_vars pe1)
				val var2 = List.first (exp_vars pe2)
				val str1 = Var.toString var1
				val str2 = Var.toString var2
				val index1 = String.substring (str1, 2, (String.length str1)-2)
				val index2 = String.substring (str2, 2, (String.length str2)-2)
			in index1 > index2 end
		
		fun getFunversion_pexpr pe funparamvars = case pe of 
			PInt n => (NONE)
		  | PVar x => (NONE)
		  | FunApp (f, pexp) => if (String.hasPrefix (f, {prefix ="P"})) then 
		  							(*if ((List.length pexp) > 1) then assertfalse ()
		  							else*)
		  							let val p = List.first pexp
		  							in
				  						case p of 
				  							PVar var => if (List.exists (funparamvars, fn p => Var.logic_equals (p, var)))
				  										then (SOME pe)
				  										else (NONE) 
				  							| _ => (NONE) 
				  					end
		  						else (NONE)
		  | Binop (p, opr, q) =>
		      let val (nl) = getFunversion_pexpr p funparamvars
		      	  val (nr) = getFunversion_pexpr q funparamvars
		      in 
		      	  case (nl, nr) of 
					(SOME nl, SOME nr) => if (varIndexGreat nl nr) then (SOME nl) else (SOME nr)
					| (SOME nl, NONE) => (SOME nl)
					| (NONE, SOME nr) => (SOME nr)
					| (NONE, NONE) => (NONE) 
		      end   
		  | Field (f, pexp) => let val (nr) = getFunversion_pexpr pexp funparamvars 
		  					   in (nr) end
		  | Proj (n, pexp) => let val (nr) = getFunversion_pexpr pexp funparamvars
		  					  in (nr) end
		  | Tuplelist pexprlist => (NONE)
		
		fun getFunversion pred funparamvars = case pred of
		    True => (NONE)
		  | Atom (p, rel, q) => let val (nl) = (getFunversion_pexpr p funparamvars) 
		  							val (nr) = (getFunversion_pexpr q funparamvars)
		  						in
		  							case (nl, nr) of 
		  								(SOME nl, SOME nr) => if (varIndexGreat nl nr) then (SOME nl) else (SOME nr)
		  								| (SOME nl, NONE) => (SOME nl)
		  								| (NONE, SOME nr) => (SOME nr)
		  								| (NONE, NONE) => (NONE)
		  						end
		  | Iff (px, q) => let val (nl) = getFunversion_pexpr px funparamvars
		  					   val (nr) = getFunversion q funparamvars
		  				   in
		  				   	   case (nl, nr) of 
	  								(SOME nl, SOME nr) => if (varIndexGreat nl nr) then (SOME nl) else (SOME nr)
	  								| (SOME nl, NONE) => (SOME nl)
	  								| (NONE, SOME nr) => (SOME nr)
	  								| (NONE, NONE) => (NONE)
		  				   end
		  | Not p => let val (nl) = getFunversion p funparamvars
		  			 in (nl) end
		  | And (p, q) => let val (nl) = (getFunversion p funparamvars) 
  							  val (nr) = (getFunversion q funparamvars)
  						  in
  						  	  case (nl, nr) of 
  								   (SOME nl, SOME nr) => if (varIndexGreat nl nr) then (SOME nl) else (SOME nr)
  								   | (SOME nl, NONE) => (SOME nl)
  								   | (NONE, SOME nr) => (SOME nr)
  								   | (NONE, NONE) => (NONE)
  						  end
		  | Or (p, q) => let val (nl) = (getFunversion p funparamvars) 
  							 val (nr) = (getFunversion q funparamvars)
  						 in
  						  	  case (nl, nr) of 
  								   (SOME nl, SOME nr) => if (varIndexGreat nl nr) then (SOME nl) else (SOME nr)
  								   | (SOME nl, NONE) => (SOME nl)
  								   | (NONE, SOME nr) => (SOME nr)
  								   | (NONE, NONE) => (NONE)
  						 end
		
		(* Compress all functions into vars *)
		fun compressHOFunTermToVar pred = 
			let val rec compressFun_pexpr = fn 
					PInt n => (PInt n, [])
				  | PVar x => (PVar x, [])
				  | FunApp (f, pexp) => if (String.hasPrefix (f, {prefix ="P"})) then 
				  							(*if ((List.length pexp) > 1) then assertfalse ()
				  							else*) 
			  								let val pexpr = List.first pexp
			  								in
			  									case pexpr of 
			  										PVar var => let val var = Var.fromString (f ^ (Var.toString var) ^ "_")
			  														val pvar = PVar var
			  													in (pvar, [(var, FunApp (f, pexp))]) end
			  										| _ => assertfalse ()
			  								end
				  						else (FunApp (f, pexp), [])
				  | Binop (p, opr, q) =>
				      let val (l, nl) = compressFun_pexpr p
				      	  val (r, nr) = compressFun_pexpr q
				      in (Binop (l, opr, r), nl @ nr) end  
				  | Field (f, pexp) => let val (r, nr) = compressFun_pexpr pexp 
				  					   in (Field (f, r), nr) end
				  | Proj (n, pexp) => let val (r, nr) = compressFun_pexpr pexp 
				  					  in (Proj (n, r), nr) end
				  | Tuplelist pexprlist => (Tuplelist pexprlist, [])
				
				val rec compressFun = fn
				    True => (True, [])
				  | Atom (p, rel, q) => let val (l, nl) = (compressFun_pexpr p) 
				  							val (r, nr) = (compressFun_pexpr q)
				  						in (Atom (l, rel, r), nl @ nr) end
				  | Iff (px, q) => let val (l, nl) = compressFun_pexpr px
				  					   val (r, nr) = compressFun q
				  				   in (Iff (l, r), nl @ nr) end
				  | Not p => let val (l, nl) = compressFun p
				  			 in (Not l, nl) end
				  | And (p, q) => let val (l, nl) = (compressFun p) 
		  							  val (r, nr) = (compressFun q)
		  						  in (And (l, r), nl @ nr) end
				  | Or (p, q) => let val (l, nl) = (compressFun p) 
		  							 val (r, nr) = (compressFun q)
		  						 in (Or (l, r), nl @ nr) end
   			in
   				compressFun pred
   			end
   			
   		fun hasHovConstraint pred = 
   			let val rec hasHovConstraint_pexpr = fn 
					PInt n => false
				  | PVar x => false
				  | FunApp (f, pexp) => if (String.hasPrefix (f, {prefix ="P"})) then 
				  							(*if ((List.length pexp) > 1) then assertfalse ()
				  							else*) 
			  								let val pexpr = List.first pexp
			  								in
			  									case pexpr of 
			  										PVar var => true
			  										| _ => assertfalse ()
			  								end
				  						else false
				  | Binop (p, opr, q) =>
				      let val l = hasHovConstraint_pexpr p
				      	  val r = hasHovConstraint_pexpr q
				      in l orelse r end  
				  | Field (f, pexp) => hasHovConstraint_pexpr pexp 
				  | Proj (n, pexp) => hasHovConstraint_pexpr pexp 
				  | Tuplelist pexprlist => false
				
				val rec hasHovConstraint = fn
				    True => false 
				  | Atom (p, rel, q) => let val l = (hasHovConstraint_pexpr p) 
				  							val r = (hasHovConstraint_pexpr q)
				  						in l orelse r end
				  | Iff (px, q) => let val l = hasHovConstraint_pexpr px
				  					   val r = hasHovConstraint q
				  				   in l orelse r end
				  | Not p => hasHovConstraint p
				  | And (p, q) => let val l = (hasHovConstraint p) 
		  							  val r = (hasHovConstraint q)
		  						  in l orelse r end
				  | Or (p, q) => let val l = (hasHovConstraint p) 
		  							 val r = (hasHovConstraint q)
		  						 in l orelse r end
   			in
   				hasHovConstraint pred
   			end
  		
  		fun last_Not_Or pred = 
  			case pred of
  				Or (Not _, p) =>
  					last_Not_Or p
  				| _ => pred 	 
	
		fun share pred1 pred2 = 
			let val pred1vars = vars pred1
				val pred2vars = vars pred2
			in
				List.exists (pred1vars, fn pv1 => (List.exists (pred2vars, fn pv2 => Var.logic_equals (pv1, pv2))))
			end
			
		fun containFunversion_pexpr pe = case pe of 
			PInt n => false
		  | PVar x => false
		  | FunApp (f, pexp) => String.hasPrefix (f, {prefix ="P"})
		  | Binop (p, opr, q) =>
		      let val (nl) = containFunversion_pexpr p
		      	  val (nr) = containFunversion_pexpr q
		      in nl orelse nr end  
		  | Field (f, pexp) => let val (nr) = containFunversion_pexpr pexp 
		  					   in (nr) end
		  | Proj (n, pexp) => let val (nr) = containFunversion_pexpr pexp
		  					  in (nr) end
		  | Tuplelist pexprlist => false
		
		fun containFunversion pred = case pred of
		    True => false
		  | Atom (p, rel, q) => let val (nl) = (containFunversion_pexpr p) 
		  							val (nr) = (containFunversion_pexpr q)
		  						in nl orelse nr end
		  | Iff (px, q) => let val (nl) = containFunversion_pexpr px
		  					   val (nr) = containFunversion q
		  				   in nl orelse nr end
		  | Not p => let val (nl) = containFunversion p
		  			 in (nl) end
		  | And (p, q) => let val (nl) = (containFunversion p) 
  							  val (nr) = (containFunversion q)
  						  in nl orelse nr end
		  | Or (p, q) => let val (nl) = (containFunversion p) 
  							 val (nr) = (containFunversion q)
  						 in nl orelse nr end
  		
  		fun pick1 (a, b) = a				 
  		fun simplify_predicate pred = case pred of
		    True => (pred, false)
		  | Atom (p, rel, q) => (pred, false)
		  | Iff (px, q) => (Iff (px, pick1 (simplify_predicate q)), false)
		  | Not p => (Not (pick1 (simplify_predicate p)), false)
		  | And (p, q) => (And (pick1 (simplify_predicate p), pick1 (simplify_predicate q)), false)
		  | Or (p, q) => (case (p, q) of 
		  		(Not (Atom (p1, rel1, q1)), Atom (p2, rel2, q2)) => (
		  				case (rel1, rel2) of
		  					(Lt, Lt) => 
		  						if (logic_equals_pexp p1 p2) then (
		  							case p1 of
		  								PInt _ => (Or (pick1 (simplify_predicate p), pick1 (simplify_predicate q)), false)
		  								| _ => (Atom (q1, Le, q2), true)
		  						)
		  						else (Or (pick1 (simplify_predicate p), pick1 (simplify_predicate q)), false)
		  					| _ => (Or (pick1 (simplify_predicate p), pick1 (simplify_predicate q)), false)
		  			) 
		  		| (Not (Atom (p1, rel1, q1)), And (i, j)) => (
		  			let val (si, simi) = simplify_predicate (Or (Not (Atom (p1, rel1, q1)), i))
		  				val (sj, simj) = simplify_predicate (Or (Not (Atom (p1, rel1, q1)), j))
		  			in
		  				if (simi andalso simj) then (And (si, sj), false)
		  				else if (simi) then (And (si, (Or (Not (Atom (p1, rel1, q1)), j))), false)
		  				else if (simj) then (And ((Or (Not (Atom (p1, rel1, q1)), i)), sj), false)
		  				else (Or (p, q), false)
		  			end
		  		)
		  		| _ => (Or (pick1 (simplify_predicate p), pick1 (simplify_predicate q)), false)
		  	)
		  	
		 fun pexpr_length pexpr = case pexpr of
		 	PInt _ => 1 
		  	| PVar _ => 1
		  	| FunApp (_, pexpr_list) => 1   
		  	| Binop (p1, _, p2) => 1
		  	| Field (_, p) => 1 + pexpr_length p
		  	| Proj (_, p) => 1 + pexpr_length p
		  	| Tuplelist (pexpr_list) => 1
	end
