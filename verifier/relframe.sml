signature REL_FRAME = 
	sig	
		include ATOMS

		type substitution = Var.t * RelPredicate.relem (* for time being *)
		
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
		  (*| RFsum of Tycon.t * (Con.t * t) list * refinement (* t must be RFconstr here *)*)
		  | RFunknown
		  
		datatype variance = RInvariant | RCovariant | RContravariant
		
		val pprint: t -> string
		(*val pprint_final : t -> (Var.t -> Qualifier.t list) -> string
		val pprint_sub: substitution -> string *)
		val pprint_refinement: refinement -> string
		(*val same_shape: bool -> (t * t) -> bool*)
		val fresh_true : unit -> refinement
    (* fresh gives a new frame for given type. It takes Type Constructor to value constructor mapping. *)
		val fresh: CoreML.Type_desc.type_desc -> TyconMap.t -> t
		val fresh_without_vars: CoreML.Type_desc.type_desc -> TyconMap.t -> t
		val fresh_unconstrained: CoreML.Type_desc.type_desc -> TyconMap.t -> t
    val fresh_refinement : RelQualifier.t -> refinement
		val fresh_constructor: Con.t -> t list -> RelPredicate.rexpr -> TyconMap.t -> t list
		val instantiate: t -> t -> t
	  val instantiate_qualifiers: (string * Var.t) list -> t -> t
		val bind: CoreML.Pat.t -> t ->RelPredicate.rexpr -> TyconMap.t -> (Var.t * t) list
		(*val bind_index : CoreML.Pat.t -> t -> (Var.t * (t * string option)) list*) (* we want a string represting its index (key) *)

		(*val bind_record : CoreML.Pat.t -> t -> Var.t -> (Var.t * t) list*)
		
		val apply_substitution: substitution -> t -> t
		val label_like: t -> t -> t
		(*val apply_solution: (Var.t -> Qualifier.t list) -> t -> t
		(*val refinement_conjuncts:
		  (Var.t -> Qualifier.t list) -> Predicate.pexpr -> refinement -> Predicate.t list
		val refinement_predicate:
		   (Var.t -> Qualifier.t list) -> Predicate.pexpr -> refinement -> Predicate.t*)
		val refinement_vars: t -> Var.t list*)
		val apply_refinement: refinement -> t -> t
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

    structure RP = RelPredicate
    structure RQ = RelQualifier
    structure TM = TyconMap
		
				
		type substitution = Var.t * RelPredicate.relem (* will change *)
		
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
		  (*| RFsum of Tycon.t * (Con.t * t) list * refinement (* t must be RFconstr here *)*)
		  | RFunknown
		  
		datatype variance = RInvariant | RCovariant | RContravariant

		(* empty refinement variable *)
		val empty_refinement = ([], RQconst [])
		
		(* false refinement variable *)
		val false_refinement = ([], RQconst [(Var.mk_ident "false", Var.mk_ident "V", RNot (RTrue))])

		fun unique_name v = Var.toString v

		fun pprint_refinement refi = case refi of
        (_, RQvar (id, _) ) => unique_name id
      | (subs, RQconst []) => "true"
      | (subs, RQconst quals) =>
        let 
          (* pprint should be dumb *)
         (* val preds = List.map (quals, (RQ.apply (RP.PVar (Predicate.Var.mk_ident "V"))))*)
          val preds = List.map (quals, (fn (_,_,p) => p))
          (*val preds = List.map (preds, (RP.apply_substs subs))*)
        in
           (List.fold (subs, "", (fn ((v,el),str) => str^"["^(RP.pprint_relem el)^"/"^(unique_name v)^"]")))^
           "("^(List.fold (preds, "", (fn (pred, str) => str ^ (RP.pprint pred))))^")"
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
             		| _ => fail "unexpected pat\n"
             end
     	
		and pprint_pattern_vector pats = "("^(Vector.fold (pats, "", (fn (pat, str) => (str ^ (pprint_pattern pat) ^ ", "))))^")" 
		
		and pprint_pattern_list pats = Vector.fold (pats, "", (fn (pat, str) => (str ^ (pprint_pattern pat) ^ ", "))) 

		and pprint_pattern_record pats = Vector.fold (Record.toVector pats, "", (fn ((field, ppat), str) => (str ^ "Field " ^ (Field.toString field) ^ 
															"Pat " ^ (pprint_pattern ppat))))

  fun wrap_refined q =
    case q of
        (_, RQconst []) => "true"
        | r => pprint_refinement r

  fun pprint_list l f s= String.concatWith ((List.map(l,f)),s)

  fun pprint_list2 l s = 
  let
    val prnt = fn (rf,field) => field^" : "^(pprint rf)
  in
    pprint_list l prnt ","
  end

  and pprint rf= case rf of 
      RFvar (a, r) => "{" ^ (unique_name a) ^ "|"^(wrap_refined r)^"}"
    | RFconstr (path, [], r) => "{" ^ (Tycon.toString path) ^ " | "  ^ (wrap_refined r) ^ "}" 
    | RFconstr (path, l, r) => "{ ("^(pprint_list l pprint ",")^") "^(Tycon.toString path)^" | " ^ (wrap_refined r) ^ "}"
    | RFarrow (NONE, f, f') => "{" ^ (pprint f) ^ " -> " ^ (pprint f') ^ "}"
    | RFarrow (SOME pat, f, f') => "{ {" ^ (pprint_pattern pat) ^ " : "^(pprint f)^"} -> " ^ (pprint f') ^ "}"
    | RFrecord (l, r) => "{(" ^ (pprint_list2 l "*")^") |  " ^ (wrap_refined r) ^ "}"
    | RFunknown => "[unknown]"

		fun unfoldRecursiveFrame fr tc subfs =
				case fr of				
              RFunknown => fr
            | RFvar (a, r) => fr
			    	| RFconstr (p, fs, r) => RFconstr (p, List.map (fs, fn fr => unfoldRecursiveFrame fr tc subfs), r)
			    	| RFarrow (x, f1, f2) => RFarrow (x, unfoldRecursiveFrame f1 tc subfs, unfoldRecursiveFrame f2 tc subfs)
			    	| RFrecord (fs, r) => RFrecord (List.map (fs, (fn (fr, n) => (unfoldRecursiveFrame fr tc subfs, n))), r)
			    	(*| RFsum (tc', [], r) => if (Tycon.equals (tc, tc')) then RFsum (tc, subfs, r) else fr
			    	| RFsum (tc', fs, r) => RFsum (tc', List.map (fs, fn (c, fr) => (c, unfoldRecursiveFrame fr tc subfs)), r)*)

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
            (*| (RFsum (p1, f1s, _), RFsum (p2, f2s, _)) =>
              if (List.length f1s = List.length f2s) then
                let fun shape_rec ((c1, f1), (c2, f2)) = Con.equals (c1, c2) andalso (same_shape map_vars) (f1, f2)
                in (Tycon.equals (p1, p2)) andalso (List.forall2 (f1s, f2s, shape_rec)) end
              else if (List.length f1s = 0 andalso not (List.length f2s = 0)) then 
                (Tycon.equals (p1, p2))
              else if (List.length f2s = 0 andalso not (List.length f1s = 0)) then
                (Tycon.equals (p1, p2))
              else false*)
          | (RFunknown, RFunknown) => true
          | _ => false
		  	end

		(* Instantiate the tyvars in fr with the corresponding frames in ftemplate.
		   If a variable occurs twice, it will only be instantiated with one frame; which
		   one is undefined and unimportant. *)
    (* Summarily, monomorphization so that we know R(cons,l) is
       now an int set against 'a set *)
    (* Functionality of unify procedure *)
		fun instantiate fr (* Frame.t *)
                    ftemplate (* Frame.t *) =
			let 
        val vars = ref []
				fun inst (f, ft) = case (f, ft) of
          (RFvar _ , _) =>
            let 
              val ff = List.peek ((!vars), (fn (f', _) => MLton.eq (f, f')))
            in
              case ff of
                  SOME (f', ft') => ft'  
                | NONE => (vars := (f, ft) :: (!vars); ft)
            end
        | (RFarrow (l, f1, f1'), RFarrow (_, f2, f2')) =>
            RFarrow (l, inst (f1, f2), inst (f1', f2'))
        | (RFconstr (p, l, r), RFconstr (p', l', _)) =>
            RFconstr(p, List.map2 (l, l', inst), r)
        | (RFrecord (f1s, r), RFrecord (f2s, _)) =>
            let fun inst_rec ((f1, name), (f2, _)) = (inst (f1, f2), name) 
            in RFrecord (List.map2 (f1s, f2s, inst_rec), r) end
        | (RFunknown, RFunknown) => RFunknown
        | (f1, f2) => (print ("@[Unsupported@ types@ for@ instantiation:@;<1 2>" ^ (pprint f1) ^ "@;<1 2>" ^ (pprint f2) ^ "@]@."); 
                      assertfalse ())
			in 
        inst (fr, ftemplate) 
			end
		
		(* We build fresh refinement variables*)
    (* fresh_refinementvar :open_assignment -> refinement *)
    (* refinement is [substitution list]*qualifier_expr *)
		fun fresh_refinementvar open_assn = ([], RQvar (Var.mk_ident "r", open_assn))
		fun fresh_true () = ([], RQconst ([(Var.dummy (), Var.mk_ident "rtrue", RelPredicate.RTrue)]))
		fun fresh_rfvar () = RFvar (Var.mk_ident "a", ([], RQvar (Var.mk_ident "r", RTop)))
    fun fresh_refinement q = ([],RQconst[q])
    fun add_qual_to_refn refn qual =  case refn of
        ([],RQconst l) => ([],RQconst (qual::l))
      | _ => (print "Invalid refinment\n";assertfalse())
		
		(* Create a fresh frame with the same shape as the type of [exp] using
		   [fresh_ref_var] to create new refinement variables. *)
    (* fresh_with_var_fun :(useless) ->Type_desc.t -> (unit -> refinement) -> (TyCon, Valcon list) hashtable
                            -> Frame.t *)
  fun fresh_with_var_fun vars ty fresh_ref_var tm =
    (* tyconslist = []; freshf = fresh_ref_var; t = ty *)
    let fun fresh_rec freshf tyconslist t = case t of
        Type_desc.Tvar tvar => 
          let
            val vfopt = (List.peek (!vars, (fn(v,f)=>(Tyvar.equals(v,tvar)))))
          in
            case vfopt of
              SOME (v,f) => f
            | NONE => let val fv = fresh_rfvar() in 
                (List.push (vars,(tvar,fv)); fv) end
          end
      | Type_desc.Tconstr(p, tyl) => (
        if (TM.tycon_mem tm p) then
          let
            (* foreach tyarg, generate frame.
               returns old frame if tyarg is in !vars *)
            val tyfs = List.map (tyl,(fresh_rec freshf tyconslist))
          in
            RFconstr (p,tyfs,freshf())
          end
        else
          (* Not a sum datatype. Just type. Empty refinement*)
          let
            val tyfs = List.map (tyl,(fresh_rec freshf tyconslist))
            val frame = RFconstr (p, tyfs, empty_refinement) 
            (*val _ = print ("\nRFconstr frame -- "^(pprint frame)^"\n")*)
          in
            frame
          end
      )
      | Type_desc.Tarrow(t1, t2) => RFarrow (NONE, fresh_rec freshf tyconslist t1, fresh_rec freshf tyconslist t2)
      | Type_desc.Ttuple fields => 
        let fun fresh_field mt = case mt of 
          Type_desc.Tfield (name, typ) => 
          let 
            val field_typ = fresh_rec freshf tyconslist typ 
          in 
            (field_typ, name) 
          end
          | _ => fail "Tfield expected\n"
        in RFrecord (List.map (fields, fresh_field), freshf()) end
      | _ => (print "@[Warning: Freshing unsupported type]@."; RFunknown)
    in 
      fresh_rec fresh_ref_var [] ty
    end

		(* fresh frame for given type *)
		fun fresh ty tm = 
			fresh_with_var_fun (ref []) ty (fn _ => fresh_refinementvar RTop) tm (* qvar *)

		fun fresh_unconstrained ty tm =
			fresh_with_var_fun (ref []) ty (fn _ => fresh_refinementvar RBottom) tm (* qvar *)

		fun fresh_without_vars ty tm =
			fresh_with_var_fun (ref []) ty (fn _ => empty_refinement) tm (* empty qconst *)
		
    (* creates fresh frames for constructor arguments in pattern
     * having the knowledge of frames of tyargs of current type constructor.
     * i.e., if type is 'a list, and pat is h::t, it creates frames for h and
     * t knowing the frame for ;a
     *)
    fun fresh_constructor c tyvarfs rexpr tm =
      let
        val tyvars = TM.get_tyvars_by_cstr tm c
        val _ = asserti((List.length tyvars = List.length tyvarfs),
          "valcon tyargs not same as tycon tyargs\n")
        val tyargmap = ref (List.zip (tyvars,tyvarfs))
        val argtylist = (TM.get_argtys_by_cstr tm c
          handle Not_found => (print "Unknown cons";assertfalse()))
        val rexpr = case rexpr of 
            RP.RRel(c',v) => if (Con.toString c' = "any") then RP.RRel(c,v) 
              else (asserti(Con.equals(c,c'),"Valcon mismatch\n"); rexpr)
          | _ => rexpr
        val fresh_ref = fn _ => fresh_refinementvar RTop
        val subset_ref = fresh_refinement(RQ.subset_qualifier c rexpr)
        fun cons_rec (t,flag) = 
        let
          val f = fresh_with_var_fun tyargmap t (fn _ => fresh_refinementvar RTop) tm
        in
          if (not flag) then f else (case f of
              RFconstr(tycon,fs,_) => RFconstr(tycon,fs,subset_ref)
            | _ => fail "Recursive frame not fconstr\n")
        end
      in
        (* for every ty in argtylist, create a new frame. Reuse tyvar frames. *)
        (* We do not use same frames for recursive args. Why? because relational
           properties are not satisfiable recursively *)
        List.map (argtylist,cons_rec)
      end

    (* bind is called from lightenv *)
		fun bind pat relframe rexpr tm =
			let 
				fun mbind (pat, relframe) =
					let 
						val patnode = Pat.node pat
					in
						case (patnode, relframe) of 
                (Pat.Wild, _) =>  ([], [])
              | (Pat.Var x, f) => ([], [(x, f)])
              | (Pat.Con {arg=NONE,con=c,targs=targv},_) => ([],[])(*nothing to bind here*)
              | (Pat.Con {arg=SOME pat',con=c,targs=targv},RFconstr(tycon, tyargfs, _)) =>
              (* targv are instantiated typevars *)
                let
                  val _ = asserti ((List.length tyargfs = Vector.length targv),
                    "Constructor tyargs error\n")
                  val arg_pat_list = (case Pat.node pat' of
                      Pat.Record tr => Vector.toListMap ((Record.toVector tr),snd)
                    | Pat.Tuple tl => Vector.toList tl
                    | _ => [pat'])
                  val cargfs = fresh_constructor c tyargfs rexpr tm
                  val _ = asserti ((List.length arg_pat_list = List.length cargfs), 
                    "cons args pat mismatch\n")
                in
                  (List.zip (arg_pat_list,cargfs), []) 
                end
              | (Pat.List ts, _) => ([], []) (* Currently we do not support list *)
              | (Pat.Record tr, RFrecord (fr, _)) => 
                  (List.zip(Vector.toList (Record.range tr), (List.map(fr, fn(a, b) => a))), [])
              | (Pat.Tuple ts, RFrecord (fs, _)) => 
                if ((List.length fs) = 0) then (* means unit *)
                  ([], []) (* Nothing to bind here *)
                else if ((List.length fs) > 1 andalso (Vector.length ts) = 1) then
                  ([(Vector.last ts, relframe)], [])
                else
                  (List.zip(Vector.toList ts, (List.map(fs, (fn(a, b) => a)))), [])
              | (Pat.Tuple ts, f) => ([(List.first (Vector.toList ts), f)], [])
              | _ => (print "\nRelBind pat relframe get wrong\n"; assertfalse ())
           end
		    in Common.expand mbind [(pat, relframe)] []
		    end

  (* Inserting refinements *)
  fun apply_refinement r rf = case rf of
      RFconstr (p, fl, _) => RFconstr (p, fl, r)
    | RFrecord (fs, _) => RFrecord (fs, r)
    | RFvar (a, _) => RFvar (a, r)
    | f => f

  fun map f fr = case fr of				
      RFunknown => f fr
    | RFvar (a, r) => f (RFvar (a, r))
    | RFconstr (p, fs, r) => f (RFconstr (p, List.map (fs, (map f)), r))
    | RFarrow (x, f1, f2) => f (RFarrow (x, map f f1, map f f2))
    | RFrecord (fs, r) => f (RFrecord (List.map (fs, (fn (fr, n) => (map f fr, n))), r))
		
  fun map_refinements_map f fr = case fr of 		
      RFconstr (p, fs, r) => RFconstr (p, fs, f r)
    | RFrecord (fs, r) => RFrecord (fs, f r)
    | RFvar (a, r) => RFvar (a, f r)
    | f => f
		
  fun map_refinements f fr = map (map_refinements_map f) fr

  (* Change the qualifiers so the referred variable relates to program unique var representation *)
  (* Mainly let this work for Qconst *)
  fun instantiate_qualifiers_map vars fr = case fr of 
        (subs, RQconst qs) => (subs, RQconst (List.map (qs, (fn q => case (RQ.instantiate vars q) of SOME q => q | NONE => q))))
        | r => r (* we keep Qvar intact *)

		(* So all the program variables in a quliafier is related to the one in our language representation *)
  fun instantiate_qualifiers vars fr =
    map_refinements (instantiate_qualifiers_map vars) fr

  fun label_like f f' =
    let fun label vars f f' = case (f, f') of
        (RFvar _, RFvar _) => (let val r = instantiate_qualifiers vars f in (r) end)
      | (RFunknown, RFunknown) => instantiate_qualifiers vars f
      | (RFconstr _, RFconstr _) => instantiate_qualifiers vars f
      | (RFarrow (NONE, f1, f1'), RFarrow (l, f2, f2')) =>
        RFarrow (l, label vars f1 f2, label vars f1' f2')
      | (RFarrow (SOME p1, f1, f1'), RFarrow (SOME p2, f2, f2')) => 
          let val vars' = List.map ((Pattern.bind_vars p1 p2), (fn (x, y) => (Var.toString x, y))) @ vars
          in RFarrow (SOME p2, label vars f1 f2, label vars' f1' f2') end
      | (RFrecord (f1s, r), RFrecord (f2s, _)) =>
          let fun label_rec ((f1, n), (f2, _)) = (label vars f1 f2, n) 
          in RFrecord (List.map2 (f1s, f2s, label_rec), r) end
      | _ => fail ("RFrame: Can't label\n"^(pprint f)^"\nlike\n"^(pprint f')^"\n")
    in label [] f f' end

  (* Inserting substitutions into refinements *)
  fun apply_substitution_map sub fr = case fr of 
      RFconstr (p, fs, (subs, qe)) => RFconstr (p, fs, (sub :: subs, qe))
    | RFrecord (fs, (subs, qe)) => RFrecord (fs, (sub :: subs, qe))
    | RFvar (a, (subs, qe)) => RFvar (a, (sub :: subs, qe)) 
    | f => f
  (*  Inserting susbstitutions into frames *)
  fun apply_substitution sub f = map (apply_substitution_map sub) f
	end
