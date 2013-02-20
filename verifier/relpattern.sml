
	
signature PATTERN = 
	sig
		include ATOMS
		val is_deep : CoreML.Pat.t -> bool
		val pattern_extend : CoreML.Pat.t option -> CoreML.Pat.t list
		val bind_vars : CoreML.Pat.t -> CoreML.Pat.t -> (Var.t * Var.t) list
		val bind_pexpr : CoreML.Pat.t -> Predicate.pexpr -> (Var.t * Predicate.pexpr) list
		val desugar_bind : CoreML.Pat.t -> Predicate.pexpr -> Predicate.t
		val same : (CoreML.Pat.t * CoreML.Pat.t) -> bool
		val vars : CoreML.Pat.t -> Var.t list
	end
	
structure Pattern : PATTERN = 
	struct
		open Atoms
		structure P = Predicate
		structure C = Common
		open C
		
		fun is_deep pat = case (CoreML.Pat.node pat) of 
			  CoreML.Pat.Wild => false 
		  	| CoreML.Pat.Var _ => false
		  	| _ => true
		
		fun pattern_descs l = Vector.toListMap (l, (fn p => CoreML.Pat.node p))
		
		fun pattern_extend pat = case pat of 
			  SOME pat' =>
				(case (CoreML.Pat.node pat') of
					  CoreML.Pat.Tuple tv => Vector.toList tv
					| CoreML.Pat.Var _ => [pat']
					| _ => (print "pattern_extend assertrion failure"; assertfalse ()))
			| NONE => [] 
		
		fun mbind_vars (pat1, pat2) = case (CoreML.Pat.node pat1, CoreML.Pat.node pat2) of 
			  (CoreML.Pat.Wild, _) => ([], [])
		  	| (CoreML.Pat.Var x, CoreML.Pat.Var y) => ([], [(x, y)])
		  	| (CoreML.Pat.Tuple p1s, CoreML.Pat.Tuple p2s) => (List.zip ((Vector.toList p1s), (Vector.toList p2s)), [])
		  	| (CoreML.Pat.Record p1s, CoreML.Pat.Record p2s) => 
		  		let
		  			val l1 = Vector.toListMap ((Record.toVector p1s), (fn (f, p) => p))
		  			val l2 = Vector.toListMap ((Record.toVector p2s), (fn (f, p) => p))
		  		in
		  			(List.zip (l1, l2), [])
		  		end
	  		| (CoreML.Pat.Con con1, CoreML.Pat.Con con2) => (List.zip ((pattern_extend (#arg con1)), (pattern_extend (#arg con2))), [])
		  	| _ => assertfalse ()
		
		fun bind_vars p1 p2 = C.expand mbind_vars [(p1, p2)] []
			
			
		(* Above is bind var as pat to pat; In Frame, we bind frame, as pat to frame; Now we bind pexpr, as var to pexpr*)		
		fun mapi f xs = 
			let fun mm i l = 
				  case l of [] => []
				| h::t => (f i h)::(mm (i+1) t) 
			in mm 0 xs end
		
		fun bind_pexpr pat pexp =
			let fun bind_rec ((pat, pexp), subs) = (
					(*print ("%%%Pat is " ^ (CoreML.Pat.visitPat pat) ^ " : " ^ (
						 case (CoreML.Pat.node pat) of
							CoreML.Pat.Con _ => "con"
							| CoreML.Pat.List _ => "list"
							| CoreML.Pat.Record _ => "record"
							| CoreML.Pat.Tuple _ => "tuple"
							| CoreML.Pat.Var _ => "var"
							| CoreML.Pat.Wild => "_"
							| _ => "impossible"
					));
					print ("pexp is " ^ (Predicate.pprint_pexpr pexp) ^ "\n");*)
				    case (CoreML.Pat.node pat) of
				      CoreML.Pat.Wild => subs
				    | CoreML.Pat.Var x => (x, pexp) :: subs
				    | CoreML.Pat.Tuple pats =>
					      let val pexps = mapi (fn i => fn pat => (pat, P.Proj(i+1, pexp))) (Vector.toList pats) 
					      in List.fold (pexps, subs, bind_rec) end
					| CoreML.Pat.Record pats =>
							let val pexps = Vector.map ((Record.toVector pats), fn (n, c) => (c, P.Field (Field.toString n, pexp)))	
							in Vector.fold (pexps, subs, bind_rec) end	 
				    | _ => subs
				    )
			in bind_rec ((pat, pexp), []) end
		
		fun desugar_bind pat pexp =
		  P.big_and (List.map ((bind_pexpr pat pexp), (fn (x, exp) => P.equals (P.PVar x) exp)))
		
		fun same (p1, p2) =
			case (CoreML.Pat.node p1, CoreML.Pat.node p2) of
				  (CoreML.Pat.Var x, CoreML.Pat.Var y) => Var.logic_equals (x, y)
			  	| (CoreML.Pat.Wild, CoreML.Pat.Wild) => true
			  	| (CoreML.Pat.Tuple pats1, CoreML.Pat.Tuple pats2) => List.forall2 ((Vector.toList pats1), (Vector.toList pats2), same)
			  	| (CoreML.Pat.Record pats1, CoreML.Pat.Record pats2) => List.forall2 ((Vector.toList (Record.range pats1)), Vector.toList (Record.range pats2), same) 
			  		(* should also compare name, but anyway it is not important *)
			  	| (CoreML.Pat.Con con1, CoreML.Pat.Con con2) => List.forall2 ((pattern_extend (#arg con1)), (pattern_extend (#arg con2)), same)
			  	| _ => false
			  	
		fun vars pat =
			let fun mvars pat =
					let 
						val patnode = CoreML.Pat.node pat
					in
						case patnode of 
							  CoreML.Pat.Con {arg, con, targs} => (pattern_extend arg, [])
		             		| CoreML.Pat.Const cf => assertfalse ()
		             		| CoreML.Pat.List ts => assertfalse () (* Currently we do not support list *)
		             		| CoreML.Pat.Record tr => (Vector.toList (Record.range tr), [])
		             		| CoreML.Pat.Tuple ts => (Vector.toList ts, [])
		             		| CoreML.Pat.Var x => ([], [x])
		             		| CoreML.Pat.Wild =>  ([], [])
		             		| _ => (print "does bind pat fram get wrong?"; assertfalse ())
		             end
		    in Common.expand mvars [pat] []
		    end
	end
