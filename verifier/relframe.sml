signature REL_FRAME = 
	sig	
		include ATOMS

		type substitution = Var.t * RelPredicate.rpexpr
		
		datatype open_assignment = RTop | RBottom
		
		datatype qualifier_expr =
		    RQvar of (Var.t * open_assignment)  (* Qualifier variable *)
		  | RQconst of RelQualifier.t list          (* Constant qualifier set *)
		
		type refinement = substitution list * qualifier_expr
		
		val empty_refinement: refinement
		val false_refinement: refinement
		
		datatype t =
		    RFvar of Var.t * refinement
		  | RFconstr of Tycon.t * t list * refinement
		  | RFarrow of CoreML.Pat.t option * t * t
		  | RFrecord of (t * string) list * refinement
		  | RFsum of Tycon.t * (Con.t * t) list * refinement (* t must be Fconstr here *)
		  | RFunknown
		  
		datatype variance = RInvariant | RCovariant | RContravariant
		
		val pprint: t -> string
		(*val pprint_final : t -> (Var.t -> Qualifier.t list) -> string
		val pprint_sub: substitution -> string *)
		val pprint_refinement: refinement -> string
		(*val same_shape: bool -> (t * t) -> bool*)
		val fresh_true : unit -> refinement
    (* fresh gives a new frame for given type. It takes Type Constructor to value constructor mapping. *)
		val fresh: CoreML.Type_desc.type_desc -> (Tycon.t, (Con.t * Type_desc.type_desc list) list) HashTable.hash_table -> t
		val fresh_without_vars: CoreML.Type_desc.type_desc -> (Tycon.t, (Con.t * Type_desc.type_desc list) list) HashTable.hash_table -> t
		val fresh_unconstrained: CoreML.Type_desc.type_desc -> (Tycon.t, (Con.t * Type_desc.type_desc list) list) HashTable.hash_table -> t
		(*val fresh_constructor: CoreML.Type_desc.type_desc -> t -> t list*)
		val instantiate: t -> t -> (Var.t, Var.t) HashTable.hash_table -> t
	  (*	val instantiate_qualifiers: (string * Var.t) list -> t -> t*)
		val bind: CoreML.Pat.t -> t -> (Var.t * t) list
		(*val bind_index : CoreML.Pat.t -> t -> (Var.t * (t * string option)) list*) (* we want a string represting its index (key) *)

		(*val bind_record : CoreML.Pat.t -> t -> Var.t -> (Var.t * t) list*)
		
		(*val apply_substitution: substitution -> t -> t
		val label_like: t -> t -> t
		val apply_solution: (Var.t -> Qualifier.t list) -> t -> t
		(*val refinement_conjuncts:
		  (Var.t -> Qualifier.t list) -> Predicate.pexpr -> refinement -> Predicate.t list
		val refinement_predicate:
		   (Var.t -> Qualifier.t list) -> Predicate.pexpr -> refinement -> Predicate.t*)
		val refinement_vars: t -> Var.t list
		val apply_refinement: refinement -> t -> t*)
		(*val predicate:
		  (Var.t -> Qualifier.t list) -> Predicate.pexpr -> t -> Predicate.t
		val conjuncts:
		  (Var.t -> Qualifier.t list) -> Predicate.pexpr -> t -> Predicate.t list*)
		  
		val unique_name : Var.t -> string
		
		(*val pprint_pattern : CoreML.Pat.t -> string
		
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
		
		val unfoldRecursiveFrame : t -> Tycon.t -> (Con.t * t) list -> t*)
		
		(*val funframe_pred : Var.t -> t -> Predicate.t*)
	end
	
structure RelFrame : REL_FRAME =
	struct
		open Atoms
		open Common
		
		open RelPredicate
		open RelQualifier
		
		open CoreML
		open Pat
		
				
		type substitution = Var.t * RelPredicate.rpexpr
		
		datatype open_assignment = RTop | RBottom
		
		datatype qualifier_expr =
		    RQvar of (Var.t * open_assignment)  (* Qualifier variable *)
		  | RQconst of RelQualifier.t list          (* Constant qualifier set *)
		
		type refinement = substitution list * qualifier_expr
		
		datatype t =
		    RFvar of Var.t * refinement
		  | RFconstr of Tycon.t * t list * refinement
		  | RFarrow of CoreML.Pat.t option * t * t
		  | RFrecord of (t * string) list * refinement
		  | RFsum of Tycon.t * (Con.t * t) list * refinement (* t must be Fconstr here *)
		  | RFunknown
		  
		datatype variance = RInvariant | RCovariant | RContravariant

		(* empty refinement variable *)
		val empty_refinement = ([], RQconst [])
		
		(* false refinement variable *)
		val false_refinement = ([], RQconst [(Var.mk_ident "false", Var.mk_ident "V", RNot (RTrue))])


		fun unique_name v = Var.toString v
    (* pprint should come here *)
    fun pprint f = "pprint not impl"

    fun pprint_refinement refn = "pprint_refinement not impl"
		
		fun unfoldRecursiveFrame fr tc subfs =
				case fr of				
              RFunknown => fr
            | RFvar (a, r) => fr
			    	| RFconstr (p, fs, r) => RFconstr (p, List.map (fs, fn fr => unfoldRecursiveFrame fr tc subfs), r)
			    	| RFarrow (x, f1, f2) => RFarrow (x, unfoldRecursiveFrame f1 tc subfs, unfoldRecursiveFrame f2 tc subfs)
			    	| RFrecord (fs, r) => RFrecord (List.map (fs, (fn (fr, n) => (unfoldRecursiveFrame fr tc subfs, n))), r)
			    	| RFsum (tc', [], r) => if (Tycon.equals (tc, tc')) then RFsum (tc, subfs, r) else fr
			    	| RFsum (tc', fs, r) => RFsum (tc', List.map (fs, fn (c, fr) => (c, unfoldRecursiveFrame fr tc subfs)), r)

    fun same_shape map_vars (t1, t2) =
			let 
        val vars = ref []
				fun ismapped p q = 
					let val found = List.peek ((!vars), (fn (p', q') => Var.logic_equals(p, p')))
					in
						case found of
							  SOME (p', q') => Var.logic_equals (q, q')
							| NONE => (vars := (p, q) :: (!vars); true)
					end
			in
       case (t1, t2) of
            (RFconstr(p, l, _), RFconstr(p', l', _)) => (
              if (List.length l = List.length l') then
                (Tycon.equals (p, p')) andalso (List.forall2 (l, l', (same_shape map_vars)))
              else false
            )
          | (RFvar (p, _), RFvar (p', _)) =>
              if map_vars then ismapped p p' else Var.logic_equals (p, p')
          | (RFarrow(_, i, o'), RFarrow(_, i', o'')) =>
              ((same_shape map_vars) (i, i')) andalso ((same_shape map_vars) (o', o''))
          | (RFrecord (f1s, _), RFrecord (f2s, _)) =>
              if (List.length f1s = List.length f2s) then
                let
                  fun shape_rec ((f1, _), (f2, _)) = (same_shape map_vars) (f1, f2) 
                in
                  List.forall2 (f1s, f2s, shape_rec)
                end
              else false
            | (RFsum (p1, f1s, _), RFsum (p2, f2s, _)) =>
              if (List.length f1s = List.length f2s) then
                let fun shape_rec ((c1, f1), (c2, f2)) = Con.equals (c1, c2) andalso (same_shape map_vars) (f1, f2)
                in (Tycon.equals (p1, p2)) andalso (List.forall2 (f1s, f2s, shape_rec)) end
              else if (List.length f1s = 0 andalso not (List.length f2s = 0)) then 
                (Tycon.equals (p1, p2))
              else if (List.length f2s = 0 andalso not (List.length f1s = 0)) then
                (Tycon.equals (p1, p2))
              else false
          | (RFunknown, RFunknown) => true
          | _ => false
		  	end

		(* Instantiate the tyvars in fr with the corresponding frames in ftemplate.
		   If a variable occurs twice, it will only be instantiated with one frame; which
		   one is undefined and unimportant. *)
		fun instantiate fr (* Frame.t *)
                    ftemplate (* Frame.t *)
                    polymatching_table (* (Var.t,Var.t) hash_table*) =
			let 
        val vars = ref []
				fun inst (f, ft) = (
				    case (f, ft) of
                (RFvar _, RFvar _) => 
                  let 
                    val ff = List.peek ((!vars), (fn (f', _) => MLton.eq (f, f')))
                  in
                    case ff of
                        SOME (f', ft') => f'  (* Make a major change here by He Zhu *) 
                      | NONE => (vars := (f, ft) :: (!vars); f) (* And there *)
                  end	
              | (RFvar (a, r), _) => (
                  let 
                    val _ = print ("--- instantiate gets interesting ---\n")
                    val ff = List.peek ((!vars), (fn (f', _) => MLton.eq (f, f')))
                    val fk = case r of 
                      (_, RQvar (k', _)) => SOME k'
                      | _ => NONE
                    val ftk = case ft of
                        RFconstr (_,_,(_, RQvar (k',_))) => SOME k'
                      | RFrecord (_,(_, RQvar (k',_))) => SOME k'
                      | RFarrow _ => NONE
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
				      | (RFarrow (l, f1, f1'), RFarrow (_, f2, f2')) => (
				      		RFarrow (l, inst (f1, f2), inst (f1', f2'))
				      		)
				      | (RFconstr (p, l, r), RFconstr (p', l', _)) => (
				      		RFconstr(p, List.map2 (l, l', inst), r)
				      		)
				      | (RFrecord (f1s, r), RFrecord (f2s, _)) =>
				      		let fun inst_rec ((f1, name), (f2, _)) = (inst (f1, f2), name) 
				      		in RFrecord (List.map2 (f1s, f2s, inst_rec), r) end
				      | (RFsum (tycon, f1s, r), RFsum (_, f2s, _)) =>
				      		let fun inst_rec ((c, f1), (_, f2)) = (c, inst (f1, f2)) 
				      		in RFsum (tycon, (List.map2 (f1s, f2s, inst_rec)), r) end
				      | (RFconstr (p1, f1s, r1), RFsum (_, f2s, _)) =>
							let 
								val f2 = List.peek (f2s, fn (c, cf) => same_shape true (f, cf))
								val f2 = case f2 of SOME (c2, f2) => f2 | NONE => (print ("\nIll typed constructor" ^ (pprint f) ^ "\n"); assertfalse ())
								val f2 = unfoldRecursiveFrame f2 p1 f2s
							in case f2 of 
								RFconstr (p2, f2s, r2) => RFconstr (p1, List.map2 (f1s, f2s, inst), r1)
								| _ => (print "\nSum type error\n"; assertfalse ())
							end
					  | (RFsum (_, f1s, _), RFconstr (p2, f2s, r2)) =>
					  		let val f1 = List.peek (f1s, fn (c, cf) => same_shape true (cf, ft))
					  			val f1 = case f1 of SOME (c1, f1) => f1 | NONE => (print ("\nIll typed constructor" ^ (pprint ft) ^ "\n"); assertfalse ())
					  			val f1 = unfoldRecursiveFrame f1 p2 f1s
					  		in case f1 of 
					  			RFconstr (p1, f1s, r1) => RFconstr (p1, List.map2 (f1s, f2s, inst), r1)
					  			| _ => (print "\nSum type error\n"; assertfalse ())
					  		end
				      | (RFunknown, RFunknown) => RFunknown
				      | (f1, f2) => (print ("@[Unsupported@ types@ for@ instantiation:@;<1 2>" ^ (pprint f1) ^ "@;<1 2>" ^ (pprint f2) ^ "@]@."); 
				      							assertfalse ())
				)
			in 
        inst (fr, ftemplate) 
			end
		
		
		(* We build fresh refinement variables*)
    (* fresh_refinementvar :open_assignment -> refinement *)
    (* refinement is [substitution list]*qualifier_expr *)
		fun fresh_refinementvar open_assn = ([], RQvar (Var.mk_ident "k", open_assn))
		fun fresh_true () = ([], RQconst ([(Var.dummy (), Var.mk_ident "true", RelPredicate.RTrue)]))
		fun fresh_rfvar () = RFvar (Var.mk_ident "a", ([], RQvar (Var.mk_ident "k", RTop)))
		
		(* Create a fresh frame with the same shape as the type of [exp] using
		   [fresh_ref_var] to create new refinement variables. *)
    (* fresh_with_var_fun :(useless) ->Type_desc.t -> (unit -> refinement) -> (TyCon, Valcon list) hashtable
                            -> Frame.t *)
		fun fresh_with_var_fun vars ty fresh_ref_var datatypeTable =
      (* tyconslist = []; freshf = fresh_ref_var; t = ty *)
			let fun fresh_rec freshf tyconslist t = 
		    	case t of
		        	  Type_desc.Tvar tvar => fresh_rfvar ()
		      		| Type_desc.Tconstr(p, tyl) => (
                  if (HashTable.inDomain datatypeTable p) then (
                    let 
                      val conlist = HashTable.lookup datatypeTable p
                      val fs = 
                        if (List.exists (tyconslist, fn ty_cons => Tycon.equals (ty_cons, p))) then
                          []
                        else
                          List.map (conlist, fn (con, tylist) => (* analyze *)
                            (con, RFconstr (p, (List.map (tylist, (fresh_rec freshf (p::tyconslist)))), freshf()))
                          )
                    in
                      RFsum (p, fs, freshf()) 
                    end
                  )
                  else
                    (* Not a sum datatype. Just type. *)
                    let
                      val frame = RFconstr (p, (List.map (tyl, (fresh_rec freshf tyconslist))), freshf()) 
                      (*val _ = print ("\nFconstr frame -- "^(pprint frame)^"\n")*)
                    in
                      frame
                    end
                )
		      		| Type_desc.Tarrow(t1, t2) => RFarrow (NONE, fresh_rec freshf tyconslist t1, fresh_rec freshf tyconslist t2)
		      		| Type_desc.Ttuple fields => 
			      		let fun fresh_field mt = case mt of 
			      			  Type_desc.Tfield (name, typ) => let val field_typ = fresh_rec freshf tyconslist typ in (field_typ, name) end
			      			| _ => assertfalse ()
			      		in RFrecord (List.map (fields, fresh_field), freshf()) end
		      		| _ => (print "@[Warning: Freshing unsupported type]@."; RFunknown)
		    in fresh_rec fresh_ref_var [] ty
		    end
		
		fun fresh ty datatypeTable = 
			fresh_with_var_fun (ref []) ty (fn _ => fresh_refinementvar RTop) datatypeTable (* qvar *)
		fun fresh_unconstrained ty datatypeTable =
			fresh_with_var_fun (ref []) ty (fn _ => fresh_refinementvar RBottom) datatypeTable (* qvar *)
		fun fresh_without_vars ty datatypeTable =
			fresh_with_var_fun (ref []) ty (fn _ => empty_refinement) datatypeTable (* empty qconst *)
		
    (* bind is called from lightenv *)
		fun bind pat relframe =
			let 
				fun mbind (pat, relframe) =
					let 
						val patnode = Pat.node pat
					in
						case (patnode, relframe) of 
							  (* Note: f should be a constructor relframe, parameter type_desc is a list 
							   * arg is the parameters for the constructor. Ideally it should be a tuple or just 
							   * one element
							   *)
                (Pat.Con {arg, con, targs}, f) => (case f of 
                    RFsum (tycon, fs, _) =>
                    let 
                      val cf = List.peek (fs, fn (c, f) => Con.equals (c, con))
                      val cf = case cf of SOME (c,f) => f | NONE => 
                        (print ("\nConstructor with ill type" ^ (CoreML.Pat.visitPat pat) ^ "\n"); assertfalse ())
                      val cf = unfoldRecursiveFrame cf tycon fs
                      val fs = case cf of RFconstr (_, fs, _) => fs | _ => 
                          (print ("\nConstrutor with ill type " ^ (pprint cf) ^ "\n"); assertfalse ()) 	
                    in	
                      (List.zip ((Pattern.pattern_extend arg), (fs)), [])
                    end
                  | RFconstr (tycon, fs, _) => 
                    if (String.equals ("::", Con.toString con)) 
                      then ([(List.first (Pattern.pattern_extend arg), List.first fs), 
                                              (List.last (Pattern.pattern_extend arg), f)], [])
                    else (print "\nShould supply a sum type\n"; assertfalse ())
                  | _ => (print "\nShould supply a sum type\n"; assertfalse ())
                  )
              | (Pat.Const cf, f) => assertfalse ()
              | (Pat.List ts, _) => ([], []) (* Currently we do not support list *)
              | (Pat.Record tr, RFrecord (fr, _)) => 
                  (List.zip(Vector.toList (Record.range tr), (List.map(fr, fn(a, b) => a))), [])
              | (Pat.Tuple ts, RFrecord (fs, _)) => 
                if ((List.length fs) = 0) then (* means unit *)
                  ([], [(Var.mk_ident "", RFconstr(Tycon.defaultInt (), [], empty_refinement))])
                else if ((List.length fs) > 1 andalso (Vector.length ts) = 1) then (
                  ([(Vector.last ts, relframe)], [])
                )
                else ( 
                  (List.zip(Vector.toList ts, (List.map(fs, (fn(a, b) => a)))), [])
                )
              | (Pat.Tuple ts, f) => ([(List.first (Vector.toList ts), f)], [])
              | (Pat.Var x, f) => ([], [(x, f)])
              | (Pat.Wild, _) =>  ([], [])
              | _ => (print "\nBind pat relframe get wrong\n"; assertfalse ())
           end
		    in Common.expand mbind [(pat, relframe)] []
		    end
	end
