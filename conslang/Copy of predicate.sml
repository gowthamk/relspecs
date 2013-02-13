(* Author: He Zhu
 * From Computer Science Department
 * Purdue University *)
 
signature PREDICATE_STRUCTS = 
	sig
		include ATOMS
	end
	
signature PREDICATE = 
	sig
		include PREDICATE_STRUCTS
		
		datatype binop = 
		    Plus
		  | Minus
		  | Times
		  | Div
		
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
		
		val big_and: t list -> t
		val big_or: t list -> t
		val int_true: pexpr
		val int_false: pexpr
		val expand_iff: t -> t
		
		(* Replace one predicate var with an pending substitution *)
		val subst: pexpr -> Var.t -> t -> t
		
		(* pending substitution works in the predicate *)
		val apply_substs: (Var.t * pexpr) list -> t -> t
	
		val vars: t -> Var.t list
		
		(* Update some predicate var with another instance of var *)
		val instantiate_named_vars: (string * Var.t) list -> t -> t
		
		val transl_pattern_pred : PATQualifier.t -> (Var.t * Var.t * t) list
		
		val logic_equals : t -> t -> bool
		
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
		
		val imply : t -> t -> t
	end
	
functor Predicate (S: PREDICATE_STRUCTS) : PREDICATE =
	struct

		open Common
		open S
		
		open PATQualifier
		open PATPredicate
		
		datatype binop =
		    Plus
		  | Minus
		  | Times
		  | Div
		
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
		      (f ^ (print_list pprint_pexpr " " pexp))
		  | Binop (p, opr, q) =>
		      let val opstr = case opr of
		          Plus => "+"
		        | Minus => "-"
		        | Times => "*"
				| Div => "/"
		      in ((pprint_pexpr p) ^ (opstr) ^ (pprint_pexpr q)) end
		  | Field (f, pexp) =>
		      ((pprint_pexpr pexp) ^ "." ^ f)
		  | Proj (n, pexp) =>
		      ((pprint_pexpr pexp) ^ "." ^ (Int.toString n))
		  | Tuplelist pexprlist => "The following is just an intermediate repr due to sml dialect " ^ (print_list pprint_pexpr " " pexprlist)
		
		(* Print predicate expression *)
		val rec pprint = fn
		    True => "true"
		  | Atom (p, rel, q) => ((pprint_pexpr p) ^ (pprint_rel rel) ^ (pprint_pexpr q))
		  | Iff (px, q) => ((pprint_pexpr px) ^ "<=>" ^ (pprint q))
		  | Not p => ("not" ^ (pprint p))
		  | And (p, q) => ((flatten_conjuncts p) ^ "and" ^ (flatten_conjuncts q))
		  | Or (p, q) => ((flatten_disjuncts p) ^ "or" ^ (flatten_disjuncts q))
		and flatten_conjuncts = fn
		    And (And (p1, p2), And (q1, q2)) =>
		        ((flatten_conjuncts p1) ^ "and" ^ (flatten_conjuncts p2) ^
		        (flatten_conjuncts q1) ^ "and" ^ (flatten_conjuncts q2))
		  | And (And (p1, p2), q) =>
		  		((pprint q) ^ "and" ^ (flatten_conjuncts p1) ^ "and" ^ (flatten_conjuncts p2))
		  | And (q, And (p1, p2)) =>
		        ((pprint q) ^ "and" ^ (flatten_conjuncts p1) ^ "and" ^ (flatten_conjuncts p2))
		  | p => pprint p
		and flatten_disjuncts = fn
		    Or (Or (p1, p2), Or (q1, q2)) =>
		        ((flatten_disjuncts p1) ^ "or" ^ (flatten_disjuncts p2) ^
		        (flatten_disjuncts q1) ^ "or" ^ (flatten_disjuncts q2))
		  | Or (Or (p1, p2), q) =>
		  		((pprint q) ^ "or" ^ (flatten_disjuncts p1) ^ "or" ^ (flatten_disjuncts p2))
		  | Or (q, Or (p1, p2)) =>
		        ((pprint q) ^ "or" ^ (flatten_disjuncts p1) ^ "or" ^ (flatten_disjuncts p2))
		  | p => pprint p
		
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
		  
		val rec simplify_predpexpr = fn pexp =>
		  let val rec simplify_predpexpr_rec = fn
		      PVar x => PVar x
		    | FunApp (fu, e) =>
		        FunApp (fu, List.map (e, simplify_predpexpr_rec))
		    | Binop (e1, opr, e2) =>
		        Binop (simplify_predpexpr_rec e1, opr, simplify_predpexpr_rec e2)
		    | Field (f, pexp) =>
		        Field (f, simplify_predpexpr_rec pexp)
		    | Proj (n, Tuplelist li) => List.nth (li, n)
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
		
		(* We do substitution here to perform substitution in pred. Note subs are map with x (string now) 
		   as index mapped to an expression e *)
		(* (Path.t * pexpr) list -> t -> t *)
		val apply_substs = fn subs => fn pred =>
			let 
				val substitute = fn ((x, e), p) => subst e x p 
			in 
				simplify_pred (List.fold (subs, pred, substitute))
			end
		
		(* (string * Var.t) list -> t -> t *)
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
		
		fun imply p q = oro (noto p) q
		
		
		fun logic_equals_pexp pexp1 pexp2 = 
			case (pexp1, pexp2) of
				  (PVar x, PVar x') => Var.logic_equals (x, x')
				| (FunApp (fu, e), FunApp (fu', e')) => (String.compare (fu, fu') = EQUAL)
															andalso (List.forall2 (e, e', (fn (p, p') => logic_equals_pexp p p')))
				| (Binop (e1, opr, e2), Binop (e1', opr', e2')) =>
						if(String.compare (pprint_opstr opr, pprint_opstr opr') = EQUAL)
						then
							(logic_equals_pexp e1 e1') andalso (logic_equals_pexp e2 e2')
						else false
				| (Field (f, pexp), Field (f', pexp')) => 
					(String.compare (f, f') = EQUAL) andalso (logic_equals_pexp pexp pexp')
				| (Proj (n, pexp), Proj (n', pexp')) =>
					(n = n') andalso (logic_equals_pexp pexp pexp')
				| (Tuplelist pexprlist, Tuplelist pexprlist') => 
					List.forall2 (pexprlist, pexprlist', (fn (p, p') => logic_equals_pexp p p'))
				| _ => false 

		
		fun logic_equals p1 p2 =
			case (p1, p2) of 
				  (True, True) => true
				| (Atom (e1, rel, e2), Atom (e1', rel', e2')) =>
					if (String.compare (pprint_rel rel, pprint_rel rel') = EQUAL) 
					then
						(logic_equals_pexp e1 e1') andalso (logic_equals_pexp e2 e2')
					else false
				| (Iff (px, q), Iff (px', q')) => (logic_equals_pexp px px') andalso (logic_equals q q')
				| (Not p, Not p') => (logic_equals p p')
				| (And (p, q), And (p', q')) => (logic_equals p p') andalso (logic_equals q q')
				| (Or (p, q), Or (p', q')) => (logic_equals p p') andalso (logic_equals q q')
				| _ => false
	end