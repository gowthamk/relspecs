signature FRAME = 
	sig	
		include ATOMS

		type substitution = Var.t * Predicate.pexpr
		
		datatype open_assignment = Top | Bottom
		
		datatype qualifier_expr =
		    Qvar of (Var.t * open_assignment)  (* Qualifier variable *)
		  | Qconst of Qualifier.t list          (* Constant qualifier set *)
		
		type refinement = substitution list * qualifier_expr
		
		val empty_refinement: refinement
		val false_refinement: refinement
		
		datatype t =
		    Fvar of Var.t * refinement
		  | Fconstr of Tycon.t * t list * refinement
		  | Farrow of CoreML.Pat.t option * t * t
		  | Frecord of (t * string) list * refinement
		  | Fsum of Tycon.t * (Con.t * t) list * refinement (* t must be Fconstr here *)
		  | Funknown
		  
		datatype variance = Covariant | Contravariant | Invariant
		
		val pprint: t -> string
		val pprint_final : t -> (Var.t -> Qualifier.t list) -> string
		val pprint_sub: substitution -> string
		val pprint_refinement: refinement -> string
		val same_shape: bool -> (t * t) -> bool
		val fresh_true : unit -> refinement
    (* fresh gives a new frame for given type. It takes Type Constructor to value constructor mapping. *)
		val fresh: CoreML.Type_desc.type_desc -> TyconMap.t -> t
		val fresh_without_vars: CoreML.Type_desc.type_desc -> TyconMap.t -> t
		val fresh_unconstrained: CoreML.Type_desc.type_desc -> TyconMap.t -> t
		val fresh_constructor: Con.t -> t -> TyconMap.t -> t list
		val instantiate: t -> t -> (Var.t, Var.t) HashTable.hash_table -> t
		val instantiate_qualifiers: (string * Var.t) list -> t -> t
		val bind: CoreML.Pat.t -> t -> (Var.t * t) list
		val new_bind: CoreML.Pat.t -> t -> TyconMap.t -> (Var.t * t) list
		val bind_index : CoreML.Pat.t -> t -> (Var.t * (t * string option)) list (* we want a string represting its index (key) *)
		val bind_record : CoreML.Pat.t -> t -> Var.t -> (Var.t * t) list
		
		val apply_substitution: substitution -> t -> t
		val label_like: t -> t -> t
		val apply_solution: (Var.t -> Qualifier.t list) -> t -> t
		(*val refinement_conjuncts:
		  (Var.t -> Qualifier.t list) -> Predicate.pexpr -> refinement -> Predicate.t list
		val refinement_predicate:
		   (Var.t -> Qualifier.t list) -> Predicate.pexpr -> refinement -> Predicate.t*)
		val refinement_vars: t -> Var.t list
		val apply_refinement: refinement -> t -> t
		(*val predicate:
		  (Var.t -> Qualifier.t list) -> Predicate.pexpr -> t -> Predicate.t
		val conjuncts:
		  (Var.t -> Qualifier.t list) -> Predicate.pexpr -> t -> Predicate.t list*)
		  
		val unique_name : Var.t -> string
		
		val pprint_pattern : CoreML.Pat.t -> string
		
		(*val pprint_with_solution : t -> (Var.t -> Qualifier.t list) -> string*)
		
		val arrowframe_refinement_vars : t -> Var.t list
		val arrowframe_parameter_refinement_vars : t -> Var.t list
		val arrowframe_pats : t -> CoreML.Pat.t list
		
		val getFrowRefVar : t -> Var.t list
		
		val getFrowFr : t -> t 
		val getFrowFr_rightversion : t -> t
		
		val queryExistenceFromArrowFrame : t -> Var.t -> bool
		
		val funFramevars : t -> Var.t list
		
		val hofunFramevars : t -> Var.t -> Predicate.pexpr list
		
		val hofunFramevars_in_version : t -> Predicate.pexpr list
		
		val hofunFramevars_in_version_2 : Var.t -> t -> Predicate.pexpr list
		
		val unfoldRecursiveFrame : t -> Tycon.t -> (Con.t * t) list -> t
		
		(*val funframe_pred : Var.t -> t -> Predicate.t*)
	end
	
structure Frame : FRAME =
	struct
		open Atoms
		open Common
		
		open Predicate
		open Qualifier
		
		open CoreML
		open Pat
    structure TM = TyconMap
		
				
		(* a variable later could be replace by an expression. In order to be efficient, expression is represented by predicate.pexpr *)
		type substitution = Var.t * Predicate.pexpr
		
		datatype open_assignment = Top | Bottom
		
		(* refinements *)
		datatype qualifier_expr =
		    Qvar of (Var.t * open_assignment)  (* Qualifier variable *)
		  | Qconst of Qualifier.t list         (* Constant qualifier set *)
		
		(* a qualifier variable with pending substitution *)
		type refinement = substitution list * qualifier_expr
		
		(* templates; Note record is like "val bar =  {x=0, y=3.14, s=ref ""}" *)
		datatype t =
		    Fvar of Var.t * refinement
		  | Fconstr of Tycon.t * t list * refinement
		  | Farrow of Pat.t option * t * t
		  | Frecord of (t * string) list * refinement
		  | Fsum of Tycon.t * (Con.t * t) list * refinement (* t must be Fconstr here *)
		  | Funknown
		  
		datatype variance = Covariant | Contravariant | Invariant
		  		
		fun pprint_sub (path, pexp) = "@[" ^ Var.toString path ^ "@ ->@ " ^ (Predicate.pprint_pexpr pexp) ^ "@]"
		
		fun pprint_subs ppf subs = List.fold (subs, "", (fn (sub, str) => str ^ (pprint_sub sub))) 
		
		fun unique_name v = Var.toString v
		
		fun pprint_refinement refi =
		  case refi of
		      (_, Qvar (id, _) ) => unique_name id
		    | (subs, Qconst []) => "true"
		    | (subs, Qconst quals) =>
		      let val preds = List.map (quals, (Qualifier.apply (Predicate.PVar (Predicate.Var.mk_ident "V"))))
		      in
		      	let val preds = List.map (preds, (Predicate.apply_substs subs))
		      	in List.fold (preds, "", (fn (pred, str) => str ^ (Predicate.pprint pred))) end
		      end
		
		fun pprint_pattern pat = 
			let val patnode = Pat.node pat
			in
				case patnode of 
					  Con {arg, con, targs} => (CoreML.Con.toString con) ^ (case arg of SOME p' => pprint_pattern p' | NONE => "")
             		| Const f => CoreML.Const.toString (f())
             		| List ts => pprint_pattern_list ts
             		| Record tr => pprint_pattern_record tr
             		| Tuple ts => pprint_pattern_vector ts
             		| Var var => CoreML.Var.toString var
             		| Wild =>  "_"
             		| _ => assertfalse () 
             end
     	
		and pprint_pattern_vector pats = "("^(Vector.fold (pats, "", (fn (pat, str) => (str ^ (pprint_pattern pat) ^ ", "))))^")" 
		
		and pprint_pattern_list pats = Vector.fold (pats, "", (fn (pat, str) => (str ^ (pprint_pattern pat) ^ ", "))) 

		and pprint_pattern_record pats = Vector.fold (Record.toVector pats, "", (fn ((field, ppat), str) => (str ^ "Field " ^ (Field.toString field) ^ 
															"Pat " ^ (pprint_pattern ppat))))
	

		fun refinement_is_empty q =
			case q of
				  (_, Qconst []) => true
				| _ => false
		
		fun wrap_refined q =
			case q of
				  (_, Qconst []) => "true"
		  		| r => pprint_refinement r
		
		fun pprint frame = 
			case frame of 
          Fvar (a, r) => "{" ^ (unique_name a) ^ "|"^(wrap_refined r)^"}"
        | Fconstr (path, [], r) => "{" ^ (Tycon.toString path) ^ " | "  ^ (wrap_refined r) ^ "}" 
        | Fconstr (path, l, r) => "{ ("^(pprint_list  "," l)^") "^(Tycon.toString path)^" | " ^ (wrap_refined r) ^ "}"
        | Farrow (NONE, f, f') => "{" ^ (pprint f) ^ " -> " ^ (pprint f') ^ "}"
        | Farrow (SOME pat, f, f') => "{ {" ^ (pprint_pattern pat) ^ " : "^(pprint f)^"} -> " ^ (pprint f') ^ "}"
        | Frecord (l, r) => "{(" ^ (pprint_list2 "*" l)^") |  " ^ (wrap_refined r) ^ "}"
        | Fsum (path, l, r) => "{" ^ (Tycon.toString path) ^ " : [" ^ (pprint_list3 "+" l) ^ "] | " ^ (wrap_refined r) ^ "}"
        | Funknown => "[unknown]"

		 and pprint1 f = 
		 	case f of 
		 		  f as (Farrow _) => "{ " ^ (pprint f) ^ " }" 
		 		| f as _  => pprint f

		 and pprint_list sep fs = let val str= List.fold (fs, "", (fn (f, str) => (str ^ (pprint f) ^ sep))) 
		 							  val str_len = String.length str
		 							  val sep_len = String.length sep
		 						  in if (str_len > sep_len) then 
		 						  		String.substring (str, 0, str_len-sep_len) 
		 						  	 else
		 						  	 	str
		 						  end
		 and pprint_list2 sep fs = let val str = List.fold (fs, "", (fn ((f, field), str) => (str ^ " " ^ field ^ " " ^ (pprint f) ^ sep))) 
		 							   val str_len = String.length str
		 							   val sep_len = String.length sep
		 						   in if (str_len > sep_len) then
		 						   		String.substring (str, 0, str_len-sep_len) 
		 						   	   else str  
		 						   end
		 and pprint_list3 sep fs = let val str = List.fold (fs, "", (fn ((c,f), str) => (str ^ (Con.toString c) ^ ":" ^ (pprint f) ^ sep))) 
		 							   val str_len = String.length str
		 							   val sep_len = String.length sep
		 						   in if (str_len > sep_len) then
		 						   		String.substring (str, 0, str_len-sep_len)
		 						   	  else str
		 						   end
		 			
		 (*=============Print out the final result ================*)
		 fun pprint_refinement_final refi sm =
		  case refi of
		      (_, Qvar (id, _) ) => (
		      (let val qs = sm id
		      in
		      	if ((List.length qs) = 0) then "true"
		      	else	
		       		let val str = List.fold (qs, "", fn ((v1, v2, p), str) => (str ^ " and " ^ (Predicate.pprint p)))
		       			val str_len = String.length str
		       		in
		       			String.substring (str, 5, str_len-5)
		       		end
		      end)
		      handle RuntimeError => "true"
		      )
		    | (subs, Qconst []) => "true"
		    | (subs, Qconst quals) =>
		      let val preds = List.map (quals, (Qualifier.apply (Predicate.PVar (Predicate.Var.mk_ident "V"))))
		      in
		      	let val preds = List.map (preds, (Predicate.apply_substs subs))
		      	in List.fold (preds, "", (fn (pred, str) => str ^ (Predicate.pprint pred))) end
		      end
		 
		 fun wrap_refined_final q sm =
			case q of
				  (_, Qconst []) => "true"
		  		| r => pprint_refinement_final r sm
		 
		 fun pprint_final frame sm = 
			case frame of 
				  Fvar (a, r) => "Var (" ^ (unique_name a) ^ " | " ^ (wrap_refined_final r sm) ^ ")"
		  		| Fconstr (path, [], r) => "{" ^ (Tycon.toString path) ^ " | "  ^ (wrap_refined_final r sm) ^ "}" 
		  		| Farrow (NONE, f, f') => "{" ^ (pprint_final1 f sm) ^ " -> " ^ (pprint_final f' sm) ^ "}"
		  		| Farrow (SOME pat, f, f') => "{" ^ (pprint_pattern pat) ^ " : " ^ (pprint_final1 f sm) ^ " -> " ^ (pprint_final1 f' sm) ^ "}"
		  		| Fconstr (path, l, r) => "{" ^ (Tycon.toString path) ^ (pprint_list_final "," l sm) ^ " | " 
		  			^ (wrap_refined_final r sm) ^ "}"
		  		| Frecord (l, r) => "(" ^ (pprint_list_final2 "*" l sm) ^ " | " ^ (wrap_refined_final r sm) ^ ")"
		  		| Fsum (path, l, r) => "{" ^ (Tycon.toString path) ^ "." ^ (pprint_list_final3 "+" l sm) ^ " | " 
		  			^ (wrap_refined_final r sm) ^ "}"
		  		| Funknown => "[unknown]"
		  		
		  and pprint_final1 f sm = 
		 	case f of 
		 		  f as (Farrow _) => "{" ^ (pprint_final f sm) ^ "}" 
		 		| f as _  => pprint_final f sm
		  and pprint_list_final sep fs sm = let val str = List.fold (fs, "", (fn (f, str) => (str ^ (pprint_final f sm) ^ sep))) 
		  										val str_len = String.length str
		 							  			val sep_len = String.length sep
		  									in if (str_len > sep_len) then 
		  											String.substring (str, 0, str_len- sep_len) 
		  										else str
		  									end
		  and pprint_list_final2 sep fs sm = let val str = List.fold (fs, "", (fn ((f, field), str) => (str ^ " " ^ field ^ " " ^ (pprint_final f sm) ^ sep)))
		  									 	 val str_len = String.length str
		  									 	 val sep_len = String.length sep
		  									 in if (str_len > sep_len) then
		  									 	 	String.substring (str, 0, str_len-sep_len) 
		  									 	else str
		  									 end 
		  and pprint_list_final3 sep fs sm = let val str = List.fold (fs, "", (fn ((c,f), str) => (str ^ (Con.toString c) ^ ":" ^ (pprint_final f sm) ^ sep))) 
				 							     val str_len = String.length str
				 							     val sep_len = String.length sep
				 						     in if (str_len > sep_len) then
				 						   		 String.substring (str, 0, str_len-sep_len)
				 						   	    else str
				 						     end
		(*==========Print out the final result ===================*)
		
		fun getFrowRefVar fr = 
			let 
				fun returnframe fr = case fr of 
					  Farrow (_, f1, f2) => (case f2 of 
					  	  Farrow _ => returnframe f2
					  	| _ => f2) 
					| _ => (print ("\nWrong frame considered as Farrow" ^ (pprint fr) ^ "\n"); assertfalse ())
				val fr = returnframe fr
				
				fun getKs fr = case fr of 
					Fconstr (_, _, (_, Qvar (k, _))) => [k]
					| Fvar (a, (_, Qvar (k, _))) => [k]
					| Frecord ([], (_, Qvar (k, _))) => [k]
					| Frecord (fs, (_, Qvar (k, _))) => (Common.flap (fn (f, name) => getKs f) fs)
					| Fsum (_, fs, (_, Qvar (k, _))) => [k]
					| Farrow _ => getFrowRefVar fr
					| _ => []
					(*| _ => (
						print ("\nCurrent tool doest support function returning a record\n"); 
						assertfalse ()
						) *)
					
			in
				getKs fr
			end
			
		fun getFrowFr fr = 
			let 
				fun returnframe fr = case fr of 
					  Farrow (_, f1, f2) => (case f2 of 
					  	  Farrow _ => returnframe f2
					  	| _ => f2) 
					| _ => assertfalse ()
			in
				returnframe fr
			end
		fun getFrowFr_rightversion fr = 
			let 
				fun returnframe fr = case fr of 
					  Farrow (SOME _, f1, f2) => (case f2 of 
					  	  Farrow (SOME _, _, _) => returnframe f2
					  	| _ => f2) 
					| _ => assertfalse ()
			in
				returnframe fr
			end
			
		fun unfoldRecursiveFrame fr tc subfs =
				case fr of				
					  Funknown => fr
					| Fvar (a, r) => fr
			    	| Fconstr (p, fs, r) => Fconstr (p, List.map (fs, fn fr => unfoldRecursiveFrame fr tc subfs), r)
			    	| Farrow (x, f1, f2) => Farrow (x, unfoldRecursiveFrame f1 tc subfs, unfoldRecursiveFrame f2 tc subfs)
			    	| Frecord (fs, r) => Frecord (List.map (fs, (fn (fr, n) => (unfoldRecursiveFrame fr tc subfs, n))), r)
			    	| Fsum (tc', [], r) => if (Tycon.equals (tc, tc')) then Fsum (tc, subfs, r) else fr
			    	| Fsum (tc', fs, r) => Fsum (tc', List.map (fs, fn (c, fr) => (c, unfoldRecursiveFrame fr tc subfs)), r)
		
		fun same_shape map_vars (t1, t2) =
			let val vars = ref []
				fun ismapped p q = 
					let val found = List.peek ((!vars), (fn (p', q') => Var.logic_equals(p, p')))
					in
						case found of
							  SOME (p', q') => Var.logic_equals (q, q')
							| NONE => (vars := (p, q) :: (!vars); true)
					end
			in
				   case (t1, t2) of
			  			  (Fconstr(p, l, _), Fconstr(p', l', _)) => (
			  			  	print ("\nl size is " ^ (Int.toString (List.length l)));
			  			  	print ("\nl' size is " ^ (Int.toString (List.length l')));
			  			  	print ("\nt1 is " ^ (pprint t1) ^ "\n");
			  			  	print ("\nt2 is " ^ (pprint t2) ^ "\n");
			  			  	if (List.length l = List.length l') then
			   					(Tycon.equals (p, p')) andalso (List.forall2 (l, l', (same_shape map_vars)))
			   				(*else if (List.length l = 0 andalso not (List.length l' = 0)) then 
			   					(Tycon.equals (p, p'))
			   				else if (List.length l' = 0 andalso not (List.length l = 0)) then
			  					(Tycon.equals (p, p'))*)
			  				else false
			  			)
			  			| (Fvar (p, _), Fvar (p', _)) =>
			   				if map_vars then ismapped p p' else Var.logic_equals (p, p')
			  			| (Farrow(_, i, o'), Farrow(_, i', o'')) =>
			   				((same_shape map_vars) (i, i')) andalso ((same_shape map_vars) (o', o''))
			  			| (Frecord (f1s, _), Frecord (f2s, _)) =>
			      			if (List.length f1s = List.length f2s) then
				      			let fun shape_rec ((f1, _), (f2, _)) = (same_shape map_vars) (f1, f2) 
				      			in
				        			List.forall2 (f1s, f2s, shape_rec)
				        		end
			        		else false
			        	| (Fsum (p1, f1s, _), Fsum (p2, f2s, _)) =>
			        		if (List.length f1s = List.length f2s) then
			        			let fun shape_rec ((c1, f1), (c2, f2)) = Con.equals (c1, c2) andalso (same_shape map_vars) (f1, f2)
			   					in (Tycon.equals (p1, p2)) andalso (List.forall2 (f1s, f2s, shape_rec)) end
			   				else if (List.length f1s = 0 andalso not (List.length f2s = 0)) then 
			   					(Tycon.equals (p1, p2))
			   				else if (List.length f2s = 0 andalso not (List.length f1s = 0)) then
			  					(Tycon.equals (p1, p2))
			  				else false
			  			| (Funknown, Funknown) => true
			  			| _ => false
		  	end 
		
		(* empty refinement variable *)
		val empty_refinement = ([], Qconst [])
		
		(* false refinement variable *)
		val false_refinement = ([], Qconst [(Var.mk_ident "false", Var.mk_ident "V", Predicate.Not (Predicate.True))])
		
		(* The following three work together to take function f on the refinement variable *)
		fun map f fr =
			case fr of				
				  Funknown => f fr
				| Fvar (a, r) => f (Fvar (a, r))
		    	| Fconstr (p, fs, r) => f (Fconstr (p, List.map (fs, (map f)), r))
		    	| Farrow (x, f1, f2) => f (Farrow (x, map f f1, map f f2))
		    	| Frecord (fs, r) => f (Frecord (List.map (fs, (fn (fr, n) => (map f fr, n))), r))
		    	| Fsum (p, fs, r) => f (Fsum (p, List.map (fs, fn (c, cf) => (c, map f cf)), r))
		
		fun map_refinements_map f fr = case fr of 		
		    Fconstr (p, fs, r) => Fconstr (p, fs, f r)
		  | Frecord (fs, r) => Frecord (fs, f r)
		  | Fvar (a, r) => Fvar (a, f r)
		  | f => f
		
		fun map_refinements f fr = map (map_refinements_map f) fr
		
		(* Instantiate the tyvars in fr with the corresponding frames in ftemplate.
		   If a variable occurs twice, it will only be instantiated with one frame; which
		   one is undefined and unimportant. *)
    (* Summarily, this function monomorphizes identifier *)
		fun instantiate fr (* Frame.t *)
                    ftemplate (* Frame.t *)
                    polymatching_table (* (Var.t,Var.t) hash_table*) =
			let val vars = ref []
				fun inst (f, ft) = (
				    case (f, ft) of
				      (Fvar _, Fvar _) => 
				        let 
                  val ff = List.peek ((!vars), (fn (f', _) => MLton.eq (f, f')))
							  in
                  case ff of
                      SOME (f', ft') => f'  (* Make a major change here by He Zhu *) 
                      (*GK : ft' contains refinements for current context.
                        So ft' should be returned *)
                    | NONE => (vars := (f, ft) :: (!vars); f) (* And there *)
                end	
					  | (Fvar (a, r), _) => (
					  		let val ff = List.peek ((!vars), (fn (f', _) => MLton.eq (f, f')))
					  			val fk = case r of 
					  				(_, Qvar (k', _)) => SOME k'
					  				| _ => NONE
					  			val ftk = case ft of
					  				Fconstr (_,_,(_, Qvar (k',_))) => SOME k'
					  				| Frecord (_,(_, Qvar (k',_))) => SOME k'
					  				| Farrow _ => NONE
					  				| _ => NONE
					  			val _ = case (fk, ftk) of
                    (* polymatching_table contains equivalence of refinement_vars *)
					  				(SOME fk, SOME ftk) => HashTable.insert polymatching_table (ftk, fk)
									| _ => ()
							in
								case ff of
									  SOME (f', ft') => ft'  (* Make a major change here by He Zhu *) 
									| NONE => (vars := (f, ft) :: (!vars); ft) (* And there *)
							end
							)
				      | (Farrow (l, f1, f1'), Farrow (_, f2, f2')) => (
				      		Farrow (l, inst (f1, f2), inst (f1', f2'))
				      		)
				      | (Fconstr (p, l, r), Fconstr (p', l', _)) => (
				      		Fconstr(p, List.map2 (l, l', inst), r)
				      		)
				      | (Frecord (f1s, r), Frecord (f2s, _)) =>
				      		let fun inst_rec ((f1, name), (f2, _)) = (inst (f1, f2), name) 
				      		in Frecord (List.map2 (f1s, f2s, inst_rec), r) end
				      | (Fsum (tycon, f1s, r), Fsum (_, f2s, _)) =>
				      		let fun inst_rec ((c, f1), (_, f2)) = (c, inst (f1, f2)) 
				      		in Fsum (tycon, (List.map2 (f1s, f2s, inst_rec)), r) end
				      | (Fconstr (p1, f1s, r1), Fsum (_, f2s, _)) =>
							let val _ = print ("\nft is " ^ (pprint ft) ^ "\n")
							val _ = print ("\nf is " ^ (pprint f) ^ "\n")
								val f2 = List.peek (f2s, fn (c, cf) => same_shape true (f, cf))
								val f2 = case f2 of SOME (c2, f2) => f2 | NONE => (print ("\nIll typed constructor" ^ (pprint f) ^ "\n"); assertfalse ())
								val f2 = unfoldRecursiveFrame f2 p1 f2s
								val _ = print ("\nThe found f2 from fsum is " ^ (pprint f2) ^ "\n")
							in case f2 of 
								Fconstr (p2, f2s, r2) => Fconstr (p1, List.map2 (f1s, f2s, inst), r1)
								| _ => (print "\nSum type error\n"; assertfalse ())
							end
					  | (Fsum (_, f1s, _), Fconstr (p2, f2s, r2)) =>
					  		let val f1 = List.peek (f1s, fn (c, cf) => same_shape true (cf, ft))
					  			val f1 = case f1 of SOME (c1, f1) => f1 | NONE => (print ("\nIll typed constructor" ^ (pprint ft) ^ "\n"); assertfalse ())
					  			val f1 = unfoldRecursiveFrame f1 p2 f1s
					  		in case f1 of 
					  			Fconstr (p1, f1s, r1) => Fconstr (p1, List.map2 (f1s, f2s, inst), r1)
					  			| _ => (print "\nSum type error\n"; assertfalse ())
					  		end
				      | (Funknown, Funknown) => Funknown
				      | (f1, f2) => (print ("@[Unsupported@ types@ for@ instantiation:@;<1 2>" ^ (pprint f1) ^ "@;<1 2>" ^ (pprint f2) ^ "@]@."); 
				      							assertfalse ())
				)
			in 
        inst (fr, ftemplate) 
			end
		
		(* Change the qualifiers so the referred variable relates to program unique var representation *)
		fun instantiate_qualifiers_map vars fr = 
			case fr of 
				  (subs, Qconst qs) => (subs, Qconst (List.map (qs, (fn q => case (Qualifier.instantiate vars q) of SOME q => q | NONE => q))))
		  		| r => r (* so we keep Qvar intact *)
		(* Mainly let this work for Qconst *)
		(* So all the program variables in a quliafier is related to the one in our language representation *)
		fun instantiate_qualifiers vars fr =
		  map_refinements (instantiate_qualifiers_map vars) fr
		
		(* We build fresh refinement variables*)
    (* fresh_refinementvar :open_assignment -> refinement *)
    (* refinement is [substitution list]*qualifier_expr *)
		fun fresh_refinementvar open_assn = ([], Qvar (Var.mk_ident "k", open_assn))
		fun fresh_true () = ([], Qconst ([(Var.dummy (), Var.mk_ident "true", Predicate.True)]))
		fun fresh_fvar () = Fvar (Var.mk_ident "a", ([], Qvar (Var.mk_ident "k", Top)))
		
		(* Create a fresh frame with the same shape as the type of [exp] using
		   [fresh_ref_var] to create new refinement variables. *)
    (* fresh_with_var_fun :(useless) ->Type_desc.t -> (unit -> refinement) -> (TyCon, Valcon list) hashtable
                            -> Frame.t *)
		fun fresh_with_var_fun vars ty fresh_ref_var tm =
      (* tyconslist = []; freshf = fresh_ref_var; t = ty *)
			let fun fresh_rec freshf tyconslist t =  (* We will have recursive types. And only the very top definition can be extensively formulated *)
		    	case t of
                (* For type variables, we just have frame vars *)
                Type_desc.Tvar tvar => 
                  let
                    val vfopt = (List.peek (!vars, (fn(v,f)=>(Tyvar.equals(v,tvar)))))
                  in
                    case vfopt of
                      SOME (v,f) => f
                    | NONE => let val fv = fresh_fvar() in 
                        (List.push (vars,(tvar,fv)); fv) end
                  end
              | Type_desc.Tconstr(p, tyl) => (
                if (TM.tycon_mem tm p) then
                  let
                    (* foreach tyarg, generate frame.
                       returns old frame if tyarg is in !vars *)
                    val tyfs = List.map (tyl,(fresh_rec freshf tyconslist))
                  in
                    Fconstr (p,tyfs,freshf())
                  end
                else
                  let
                    val tyfs = List.map (tyl,(fresh_rec freshf tyconslist))
                    val frame = Fconstr (p, tyfs,freshf()) 
                    (*val _ = print ("\nRFconstr frame -- "^(pprint frame)^"\n")*)
                  in
                    frame
                  end)
		      		| Type_desc.Tarrow(t1, t2) => Farrow (NONE, fresh_rec freshf tyconslist t1, fresh_rec freshf tyconslist t2)
		      		| Type_desc.Ttuple fields => 
			      		let fun fresh_field mt = case mt of 
			      			  Type_desc.Tfield (name, typ) => let val field_typ = fresh_rec freshf tyconslist typ in (field_typ, name) end
			      			| _ => assertfalse ()
			      		in Frecord (List.map (fields, fresh_field), freshf()) end
		      		| _ => (print "@[Warning: Freshing unsupported type]@."; Funknown)
		    in fresh_rec fresh_ref_var [] ty
		    end
		
		fun fresh ty tm = 
			fresh_with_var_fun (ref []) ty (fn _ => fresh_refinementvar Top) tm (* qvar *)
		fun fresh_unconstrained ty tm =
			fresh_with_var_fun (ref []) ty (fn _ => fresh_refinementvar Bottom) tm (* qvar *)
		fun fresh_without_vars ty tm =
			fresh_with_var_fun (ref []) ty (fn _ => empty_refinement) tm (* empty qconst *)
		
		(* All returned are about formal argtypes. cstrdesc should be a constructor type; 
		 * Ideally we want it to be Tconster (...)
		 * Discarded	
		fun fresh_constructor cstrdesc fr = case fr of
			  Fconstr (_, fl, _) =>
			  	let val tyargs = case cstrdesc of
					  Type_desc.Tconstr (_, args) => args
					| _ => assertfalse ()  	
					val argmap = ref (List.zip(tyargs, fl))
				in
					List.map(tyargs, (fn t => fresh_with_var_fun argmap t (fn _ => fresh_refinementvar Top)))
				end
			| _ => assertfalse ()
		*)			
    fun fresh_constructor c f tm = case f of
      Fconstr (tycon,tyvarfs,_) =>
        let
          val tyvars = TM.get_tyvars_by_cstr tm c
          val _ = asserti((List.length tyvars = List.length tyvarfs),
            "Frame : valcon tyargs not same as tycon tyargs\n")
          val tyargmap = ref (List.zip (tyvars,tyvarfs))
          val argtylist = (TM.get_argtys_by_cstr tm c
            handle Not_found => (print "Unknown cons";assertfalse()))
          val fresh_ref = fn _ => fresh_refinementvar Top
          fun cons_rec (t,flag) = 
          let
            val new_f = (fn _ => fresh_with_var_fun tyargmap t (fn _ => fresh_refinementvar Top) tm)
          in
            if (not flag) then new_f() else f (*recursive unfolding *)
          end
        in
          (* for every ty in argtylist, create a new frame. Reuse tyvar frames. *)
          (* We do not use same frames for recursive args. Why? because relational
             properties are not satisfiable recursively *)
          List.map (argtylist,cons_rec)
        end
      | _ => fail "Frame : Fconstr expected\n"
		
    (*(Pat.Con {arg, con, targs}, f) => (case f of 
                    Fsum (tycon, fs, _) =>
                      let val cf = List.peek (fs, fn (c, f) => Con.equals (c, con))
                        val cf = case cf of SOME (c,f) => f | NONE => 
                          (print ("\nConstructor with ill type" ^ (CoreML.Pat.visitPat pat) ^ "\n"); assertfalse ())
                        val _ = print ("\ncf is " ^ (pprint cf) ^ "\n")
                        val cf = unfoldRecursiveFrame cf tycon fs
                        val fs = case cf of Fconstr (_, fs, _) => fs | _ => 
                            (print ("\nConstrutor with ill type " ^ (pprint cf) ^ "\n"); assertfalse ()) 	
                      in	
                        (List.zip ((Pattern.pattern_extend arg), (fs)), [])
                      end
                    | Fconstr (tycon, fs, _) => 
                      if (String.equals ("::", Con.toString con)) then ([(List.first (Pattern.pattern_extend arg), List.first fs), 
                                                (List.last (Pattern.pattern_extend arg), f)], [])
                      else (print "\nShould supply a sum type\n"; assertfalse ())
                    | _ => (print "\nShould supply a sum type\n"; assertfalse ())
                    ) *)

		fun bind pat frame =
			let 
				fun mbind (pat, frame) =
					let (*val _ = print ("\nFrame binding pat frame with pat as " ^ (CoreML.Pat.visitPat pat) ^ " frame as " ^ (pprint frame) ^ "\n")*)
						val patnode = Pat.node pat
						(*val _ = print ("Patnode is of type " ^ (case patnode of
							Pat.Con _ => "con"
							| Pat.List _ => "list"
							| Pat.Record _ => "record"
							| Pat.Tuple _ => "tuple"
							| Pat.Var _ => "var"
							| Pat.Wild => "_"
							| _ => "impossible") ^ "\n"
							)*)
					in
						case (patnode, frame) of 
							  (* Note: f should be a constructor frame, parameter type_desc is a list 
							   * arg is the parameters for the constructor. Ideally it should be a tuple or just 
							   * one element
							   *)
							  (Pat.Con {arg, con, targs}, f) => (case f of 
					  			Fsum (tycon, fs, _) =>
					  				let val cf = List.peek (fs, fn (c, f) => Con.equals (c, con))
					  					val cf = case cf of SOME (c,f) => f | NONE => 
					  						(print ("\nConstructor with ill type" ^ (CoreML.Pat.visitPat pat) ^ "\n"); assertfalse ())
					  					val _ = print ("\ncf is " ^ (pprint cf) ^ "\n")
					  					val cf = unfoldRecursiveFrame cf tycon fs
					  					val fs = case cf of Fconstr (_, fs, _) => fs | _ => 
					  							(print ("\nConstrutor with ill type " ^ (pprint cf) ^ "\n"); assertfalse ()) 	
					  				in	
					  					(List.zip ((Pattern.pattern_extend arg), (fs)), [])
					  				end
					  			| Fconstr (tycon, fs, _) => 
					  				if (String.equals ("::", Con.toString con)) then ([(List.first (Pattern.pattern_extend arg), List.first fs), 
					  																	(List.last (Pattern.pattern_extend arg), f)], [])
					  				else (print "\nShould supply a sum type\n"; assertfalse ())
					  			| _ => (print "\nShould supply a sum type\n"; assertfalse ())
					  			)
		             		| (Pat.Const cf, f) => assertfalse ()
		             		| (Pat.List ts, _) => ([], []) (* Currently we do not support list *)
		             		| (Pat.Record tr, Frecord (fr, _)) => (List.zip(Vector.toList (Record.range tr), (List.map(fr, fn(a, b) => a))), [])
		             		| (Pat.Tuple ts, Frecord (fs, _)) => 
		             			if ((List.length fs) = 0) then (* means unit *)
		             				([], [(Var.mk_ident "", Fconstr(Tycon.defaultInt (), [], empty_refinement))])
		             			else if ((List.length fs) > 1 andalso (Vector.length ts) = 1) then (
		             				([(Vector.last ts, frame)], [])
		             			)
		             			else ( 
		             				(List.zip(Vector.toList ts, (List.map(fs, (fn(a, b) => a)))), [])
		             			)
		             		| (Pat.Tuple ts, f) => ([(List.first (Vector.toList ts), f)], [])
		             		| (Pat.Var x, f) => ([], [(x, f)])
		             		| (Pat.Wild, _) =>  ([], [])
		             		| _ => (print "\nBind pat frame get wrong\n"; assertfalse ())
		             end
		    in Common.expand mbind [(pat, frame)] []
		    end

		fun new_bind pat frame tm =
			let 
				fun mbind (pat, frame) =
					let (*val _ = print ("\nFrame binding pat frame with pat as " ^ (CoreML.Pat.visitPat pat) ^ " frame as " ^ (pprint frame) ^ "\n")*)
						val patnode = Pat.node pat
					in
						case (patnode, frame) of 
              (Pat.Con {arg=NONE,con=c,targs=targv},_) => ([],[])(*nothing to bind here*)
            | (Pat.Con {arg=SOME pat',con=c,targs=targv},Fconstr(tycon, tyargfs, _)) =>
              (* targv are instantiated typevars *)
              let
                val _ = asserti ((List.length tyargfs = Vector.length targv),
                  "Frame : Constructor tyargs error\n")
                val arg_pat_list = (case Pat.node pat' of
                    Pat.Record tr => Vector.toListMap ((Record.toVector tr),snd)
                  | Pat.Tuple tl => Vector.toList tl
                  | _ => [pat'])
                val cargfs = fresh_constructor c frame tm
                val _ = asserti ((List.length arg_pat_list = List.length cargfs), 
                  "Frame : cons args pat mismatch\n")
              in
                (List.zip (arg_pat_list,cargfs), []) 
              end
            | (Pat.Con _,Fsum _) => fail "Life gave us Fsum\n"
            | (Pat.Const cf, f) => assertfalse ()
            | (Pat.List ts, _) => ([], []) (* Currently we do not support list *)
            | (Pat.Record tr, Frecord (fr, _)) => (List.zip(Vector.toList (Record.range tr), (List.map(fr, fn(a, b) => a))), [])
            | (Pat.Tuple ts, Frecord (fs, _)) => 
              if ((List.length fs) = 0) then (* means unit *)
                ([], []) (* nothing to bind here *)
              else if ((List.length fs) > 1 andalso (Vector.length ts) = 1) then 
                ([(Vector.last ts, frame)], [])
              else
                (List.zip(Vector.toList ts, (List.map(fs, (fn(a, b) => a)))), [])
            | (Pat.Tuple ts, f) => ([(List.first (Vector.toList ts), f)], [])
            | (Pat.Var x, f) => ([], [(x, f)])
            | (Pat.Wild, _) =>  ([], [])
            | _ => (print "\nBind pat frame get wrong\n"; assertfalse ())
         end
      in Common.expand mbind [(pat, frame)] []
      end
		
		fun bind_index pat frame =
			let 
				fun mbind (pat, (frame, index)) =
					let val patnode = Pat.node pat
					in
						case (patnode, frame) of 
							  (Pat.Con {arg, con, targs}, f) => (case f of 
					  			Fsum (tycon, fs, _) =>
					  				let val cf = List.peek (fs, fn (c, f) => Con.equals (c, con))
					  					val cf = case cf of SOME (c,f) => f | NONE => 
					  						(print ("\nConstructor with ill type" ^ (CoreML.Pat.visitPat pat) ^ "\n"); assertfalse ())
					  					val _ = print ("\ncf is " ^ (pprint cf) ^ "\n")
					  					val cf = unfoldRecursiveFrame cf tycon fs
					  					val fs = case cf of Fconstr (_, fs, _) => fs | _ => 
					  							(print ("\nConstrutor with ill type " ^ (pprint cf) ^ "\n"); assertfalse ()) 	
					  				in	
					  					(List.zip (
					  						(Pattern.pattern_extend arg), 
					  						List.mapi (fs, 
					  							fn (i, f) => (f, SOME (Int.toString i))
					  							)					  						
					  						)
					  					, [])
					  				end
					  			| _ => (print "\nShould supply a sum type\n"; assertfalse ())
					  			)
		             		| (Pat.Const cf, f) => assertfalse ()
		             		| (Pat.List ts, _) => assertfalse () (* Currently we do not support list *)
		             		| (Pat.Record tr, Frecord (fr, _)) => (List.zip(Vector.toList (Record.range tr), (List.map(fr, fn(a, b) => (a, SOME b)))), [])
		             		| (Pat.Tuple ts, Frecord (fs, _)) => 
		             			if ((List.length fs) = 0) then (* means unit *)
		             				([], [(Var.mk_ident "", (Fconstr(Tycon.defaultInt (), [], empty_refinement), index))])
		             			else if ((List.length fs) > 1 andalso (Vector.length ts) = 1) then (
		             				([(Vector.last ts, (frame, index))], [])
		             			)
		             			else ( 
		             				(List.zip(Vector.toList ts, (List.map(fs, (fn(a, b) => (a, SOME b))))), [])
		             			)
		             		| (Pat.Tuple ts, f) => ([(List.first (Vector.toList ts), (f, index))], [])
		             		| (Pat.Var x, f) => ([], [(x, (f, index))])
		             		| (Pat.Wild, _) =>  ([], [])
		             		| _ => (print "\nBind pat frame get wrong\n"; assertfalse ())
		             end
		    in Common.expand mbind [(pat, (frame, NONE))] []
		    end
		    
		fun bind_record pat frame record_var =
			let 
				fun mbind (pat, frame) =
					let val _ = print ("\nFrame binding pat frame with pat as " ^ (CoreML.Pat.visitPat pat) ^ " frame as " ^ (pprint frame) ^ "\n")
						val patnode = Pat.node pat
						val _ = print ("Patnode is of type " ^ (case patnode of
							Pat.Con _ => "con"
							| Pat.List _ => "list"
							| Pat.Record _ => "record"
							| Pat.Tuple _ => "tuple"
							| Pat.Var _ => "var"
							| Pat.Wild => "_"
							| _ => "impossible") ^ "\n"
							)
					in
						case (patnode, frame) of 
              (Pat.Tuple ts, Frecord (fs, r)) => 
              if ((List.length fs) = 0) then (* means unit *)
                ([], [(Var.mk_ident "", Fconstr(Tycon.defaultInt (), [], empty_refinement))])
              else if ((List.length fs) > 1 andalso (Vector.length ts) = 1) then (
                ([(Vector.last ts, frame)], [])
              )
              else ( 
                (List.zip(Vector.toList ts, (List.map(fs, (fn(a, b) => a)))), [(record_var, Fconstr(Tycon.defaultInt (), [], r))])
              )
            | (Pat.Tuple ts, f) => ([(List.first (Vector.toList ts), f)], [])
            | _ => (print "\nFrame : Bind pat frame get wrong\n"; assertfalse ())
         end
		    in Common.expand mbind [(pat, frame)] []
		    end
		
		(* Label all the function formals in [f] with their corresponding labels in
		   [f'] and changing constant qualifiers appropriately.
		   [f] and [f'] are expected to be of the same shape; also, [f]
		   must be completely unlabeled (as frames are after creation by fresh). *)
		fun label_like f f' =
			let fun label vars f f' = case (f, f') of
				      (Fvar _, Fvar _) => (let val r = instantiate_qualifiers vars f in (r) end)
				    | (Funknown, Funknown) => instantiate_qualifiers vars f
				    | (Fconstr _, Fconstr _) => instantiate_qualifiers vars f
				    | (Farrow (NONE, f1, f1'), Farrow (l, f2, f2')) =>
				    	Farrow (l, label vars f1 f2, label vars f1' f2')
				    | (Farrow (SOME p1, f1, f1'), Farrow (SOME p2, f2, f2')) => 
				        let val vars' = List.map ((Pattern.bind_vars p1 p2), (fn (x, y) => (Var.toString x, y))) @ vars
				        in Farrow (SOME p2, label vars f1 f2, label vars' f1' f2') end
				    | (Frecord (f1s, r), Frecord (f2s, _)) =>
				        let fun label_rec ((f1, n), (f2, _)) = (label vars f1 f2, n) 
				        in Frecord (List.map2 (f1s, f2s, label_rec), r) end
				    | (Fsum (_, f1s, r), Fsum (tycon2, f2s, _)) =>
				    	let fun label_rec ((_, f1), (c, f2)) = (c, label vars f1 f2)
				    	in Fsum (tycon2, (List.map2 (f1s, f2s, label_rec)), r) end
				    | _ => (print ("Can't label " ^ (pprint f) ^ " like " ^ (pprint f')); assertfalse ())
			in label [] f f' end
		
		(* Inserting substitutions into refinements *)
		fun apply_substitution_map sub fr = 
			case fr of 
				  Fconstr (p, fs, (subs, qe)) => Fconstr (p, fs, (sub :: subs, qe))
			  	| Frecord (fs, (subs, qe)) => Frecord (fs, (sub :: subs, qe))
			  	| Fvar (a, (subs, qe)) => Fvar (a, (sub :: subs, qe)) 
			  	| f => f
		  
		(*  Inserting susbstitutions into frames *)
		fun apply_substitution sub f = map (apply_substitution_map sub) f
		
		(* Inserting predicates solutions for refinements *)
		fun refinement_apply_solution solution refinement = 
			case refinement of 
				  (subs, Qvar (k, _)) => (subs, Qconst (solution k))
		  		| r => r
		  
		(* putting solutions to each refinements *)
		fun apply_solution_map solution fr = 
			case fr of 
				  Fconstr (path, fl, r) => Fconstr (path, fl, refinement_apply_solution solution r)
		  		| Frecord (fs, r) => Frecord (fs, refinement_apply_solution solution r)
		  		| Fvar (a, r) => Fvar (a, refinement_apply_solution solution r)
		  		| f => f
		
		(* Putting solutions for the given frame *)
		fun apply_solution solution fr = map (apply_solution_map solution) fr
		
		(* The following three work together to find refinement vars *)
		fun maybe_cons m xs = 
			case m of
		  		  NONE => xs
		  		| SOME x => x :: xs
		
		fun ref_var refinement = 
			case refinement of 
				  (_, Qvar (k, _)) => SOME k
		  		| _ => NONE
		  
		(* Extracting refinement vars *)
		fun refinement_vars fr = 
			case fr of
				  Fconstr (_, _, r) => maybe_cons (ref_var r) []
		  		| Frecord (fs, r) => maybe_cons (ref_var r) (List.fold (fs, [], (fn ((f, _), r) => refinement_vars f @ r)))
		  		| Fvar (_, r) => maybe_cons (ref_var r) []
		  		| _ => []
		  		
		fun arrowframe_refinement_vars fr = (
			case fr of 
			(Farrow (_, f1, f2)) =>
				let val l1 = (case f1 of
						Farrow _ => arrowframe_refinement_vars f1
						| _ => refinement_vars f1)
					val l2 = (case f2 of 
						Farrow _ => arrowframe_refinement_vars f2
						| _ => refinement_vars f2)
				in
					l1 @ l2 
				end  
			| _ => (print "Not a function frame given in arrowframe_refinement_vars"; assertfalse ()) 
			)
			
		fun arrowframe_parameter_refinement_vars fr = (
			case fr of 
			(Farrow (_, f1, f2)) =>
				let val l1 = (case f1 of
						Farrow _ => arrowframe_parameter_refinement_vars f1
						| _ => refinement_vars f1)
					val l2 = (case f2 of 
						Farrow (SOME _, _, _) => arrowframe_parameter_refinement_vars f2
						| _ => [])
				in
					l1 @ l2 
				end  
			| _ => (print "Not a function frame given in arrowframe_refinement_vars"; assertfalse ()) 
			)
			
		fun arrowframe_pats fr = case fr of 
			(Farrow (p, f1, f2)) =>
				let val l1 = [] (*(case f1 of
						Farrow _ => arrowframe_pats f1
						| _ => [])*)
					val l2 = (case f2 of 
						Farrow _ => arrowframe_pats f2
						| _ => [])
				in
					case p of 
						  SOME pat => pat :: (l1 @ l2)
						| NONE => (print ("Insufficient pats in frame" ^ (pprint fr)); assertfalse ())  
				end  
			| _ => assertfalse () 
			
		(* Inserting refinements *)
		fun apply_refinement r fr = 
			case fr of
				  Fconstr (p, fl, _) => Fconstr (p, fl, r)
		  		| Frecord (fs, _) => Frecord (fs, r)
		  		| Fvar (a, _) => Fvar (a, r)
		  		| f => f
			
		fun queryExistenceFromArrowFrame fr kg = 
			let val ks = arrowframe_refinement_vars fr
				(*val _ = print ("\nquery existentce for k gets " ^ List.fold (ks, "", fn (k, str) => (str ^ " " ^ (Var.toString k))))
				val _ = print ("\nNow looking for k as " ^ (Var.toString kg) ^ " \n")*)
			in
				List.exists (ks, fn k => Var.logic_equals (kg, k))
			end
			
		fun funFramevars fr = 
			let fun framevars'' pat f = 
					let val varfrs = bind pat f
					in List.map (varfrs, fn (var, frame) => var) end
				fun framevars' f = 
					case f of 
				 		  Farrow (SOME ppat, f1, f2) => 
				 			let val l1 = framevars'' ppat f1
				 				val l2 = case f2 of 
				 					  Farrow _ => framevars' f2
				 					| _ => []
				 			in
				 				l1 @ l2
							end 
						| Farrow (_, f1, f2) => [] 	
						| _ => (print "Not arrow given for a frame\n"; assertfalse ())
			in
				framevars' fr
			end
			
		fun hofunFramevars fr funvar = 
			let fun framevars' f index = 
					case f of 
				 		  Farrow (_, f1, f2) => 
				 			let val l1 = [Predicate.FunApp (("arg" ^ (Int.toString index)), [Predicate.PVar funvar])]
				 				val l2 = case f2 of 
				 					  Farrow _ => framevars' f2 (index+1)
				 					| _ => []
				 			in
				 				l1 @ l2
							end 
						(*| Farrow (SOME _, f1, f2) => (print "Explicit function frame given\n"; assertfalse ())*)	
						| _ => (print "Not arrow given for a frame\n"; assertfalse ())
			in
				framevars' fr 0
			end
			
		fun hofunFramevars_in_version fr = 
			let fun framevars' f index = 
					case f of 
				 		  Farrow (_, f1, f2) => 
				 			let val l1 = [Predicate.PVar (Var.fromString ("local_arg" ^ (Int.toString index)))]
				 				(*[Predicate.FunApp (("local_arg" ^ (Int.toString index)), [Predicate.PVar funvar])]*)
				 				val l2 = case f2 of 
				 					  Farrow _ => framevars' f2 (index+1)
				 					| _ => []
				 			in
				 				l1 @ l2
							end 
						(*| Farrow (SOME _, f1, f2) => (print "Explicit function frame given\n"; assertfalse ())*)	
						| _ => (print "Not arrow given for a frame\n"; assertfalse ())
			in
				framevars' fr 0
			end
			
		fun hofunFramevars_in_version_2 funvar fr = 
			let fun framevars' f index = 
					case f of 
				 		  Farrow (_, f1, f2) => 
				 			let val l1 = [Predicate.FunApp ("arg" ^ (Int.toString index), [Predicate.PVar funvar])] 
				 				val l2 = case f2 of 
				 					  Farrow _ => framevars' f2 (index+1)
				 					| _ => []
				 			in
				 				l1 @ l2
							end 
						| _ => (print "Not arrow given for a frame\n"; assertfalse ())
			in
				framevars' fr 0
			end
		
		(* Scanning the frame to find if there is a pat with a Fconster of refinement of k *)
		(* This function is discarded 
		fun scanFrameForK fr kr = 
			let fun scan'' pat f = 
					let val varfrs = bind pat f
					in 
						List.map (List.keepAll (varfrs, fn (var, fr) => 
							case fr of 
								Fconstr (_, _, (_, Qvar (k, _))) => (
				  				  	Var.logic_equals (k, kr)
				  				)
				  				| _ => false
						), fn (a, b) => a
						)
					end 
				fun scan' fr = 
					case fr of 
						Farrow (SOME ppat, f1, f2) =>
							let val l1 = scan'' ppat f1
								val l2 = case f2 of 
									Farrow _ => scan' f2
									| _ => []
							in
								l1 @ l2
							end
						| Farrow (_, f1, f2) => []
						| _ => (print "Not arrow given for a frame when scanning\n"; assertfalse ())
				val vars = scan' fr 
			in
				if ((List.length vars) > 1) then (print ("Currently we cannot deal with this fr, please rewrite it " ^ (pprint fr)); NONE)
				else if ((List.length vars) = 1) then 
					SOME (List.first vars)
				else NONE
			end
			*)
		
		
		(*
		 * Make a pre for higher order function. Problem need to be fixed: Frecord case in this function and in BackWalk.Funsubs function
		 *)	
		(*fun funframe_pred var fr =
			let val varname = Var.toString var
				fun loop varname fr index = 
					case fr of 
						Farrow (NONE, f1, f2) => (
							let val p1 = case f1 of 
									Frecord f1s => Predicate.big_and (List.mapi (f1s, fn (i, (_, f1)) => loop (Var.fromString (varname ^ "_" ^ (Int.toString index))) f1 i))
									| _ => (Predicate.Atom (Predicate.PVar (Var.fromString (varname ^ (Int.toString index))), 
														Predicate.Eq, 
														Predicate.PVar (Var.fromString (varname ^ "_" ^ (Int.toString index)))))
								val p2 = case f2 of
									Farrow _ => loop varname f2 (index+1) 
									| _ => []
							in
								p1 :: p2
							end 
						)
						| _ => (print "\nOnly meaningful for higher order function frame\n"; assertfalse ())
			in loop varname fr 0 end*)
	end
