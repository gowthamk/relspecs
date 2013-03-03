structure RelConstraintgen (*: CONSTRAINTGEN *) = 
struct
  open Atoms
  open CoreML
  open Type_desc
  open Common
  (*open RelFrame*)
  (*open RelConstraint*)
  structure P = Predicate
  structure RP = RelPredicate
  structure RQ = RelQualifier
  structure C = Common
  structure Cf = Control
  structure Cs = Constraint
  structure RCs = RelConstraint
  structure B = Builtin
  structure RB = RelBuiltin
  structure Le = Lightenv
  structure RLe = RelLightenv
  structure F = Frame
  structure RF = RelFrame
  structure TM = TyconMap

  datatype error =
      NotSubtype of F.t * F.t
    | IllFormed of F.t
    | AssertMayFail
  
  exception Error of (Exp.t option) * error
  exception Errors of (Exp.t option * error) list

  
  val hash_fn = HashString.hashString

  fun getFunctionAppName e = 
    case (Exp.node e) of 
      Exp.App (e1, e2) => getFunctionAppName e1
      | Exp.Var (var, _) => (Var.toString (var()))
      | _ => (print ("\nError expression considered as Var " ^ (CoreML.visitExp e) ^ "\n"); assertfalse ())
      
    
  fun type_desc exp = Type.toMyType (Exp.ty exp)

  val defaultCons = Con.defaultCons

  val tycon_map = TM.new_tycon_map()

  fun filter_conargs e2 = 
    let
      fun filter_exp e = (case (Exp.node e) of
          Exp.Var (v,_) =>e
        | Exp.Const f => e
        | _ => (print ("Apply cons only on vars and consts\n");assertfalse()))
      val (conargs: (Exp.t list)) = (case (Exp.node e2) of
          Exp.Record r => 
          let
            val exp_list = Vector.toListMap (Record.toVector r,snd)
          in
            List.map (exp_list, filter_exp)
          end
        | _ => [filter_exp e2])

    in
      conargs
    end

  fun constexp_to_int e = (case (Exp.node e) of
      (Exp.Const f) => (case (type_desc e) of
          Tconstr (t, []) => 
            if (Tycon.isIntX t) then
              let val constval = f() in
                case constval of 
                     Const.IntInf n => SOME (IntInf.toInt n)
               | Const.Word n => SOME (WordX.toInt n)
               | _ => (print "toPredIntError\n"; assertfalse ())
              end  		
            else NONE
        | _ => NONE)
    | _ => fail "Const exp expected\n")

  fun expr_to_relem_list e= 
    let
      val el = filter_conargs e
    in
      List.map (el,(fn(e) => case Exp.node e of
          Exp.Var (v,_) => RP.RVar (RP.make_typedvar(v()))
        | Exp.Const f => (case constexp_to_int e of 
            SOME i => RP.RInt i
          | NONE => fail "Only integer constants allowed\n")
        ))
    end

  fun expression_to_rexpr e = case (Exp.node e) of
      Exp.Const f => (case (constexp_to_int e) of
          SOME i => RP.make_rset [RP.RInt i]
        (* This is irrelevant as we will eventually have RTrue as pat refinement *)
        | NONE => RP.make_dummy_rexpr() 
      )
    | Exp.Var (varf, _) => RP.make_rrel(defaultCons,RP.make_typedvar(varf()))
    | Exp.App (e1, e2) => (case ((type_desc e),(Exp.node e1)) of
          (Tconstr (tycon,tdlist), Exp.Con (c,_)) =>
            (let
              val (flags:(bool list)) = List.map ((TM.get_argtys_by_cstr tycon_map c), (fn(x,y)=>y)) 
              val conargs = filter_conargs e2
              val _ = if (not (List.length flags = List.length conargs))then
                  (print ("Constructor application pattern mismatch\n");assertfalse())
                else ()
              fun separate (e,flag,(l1,l2)) = (case (Exp.node e) of
                  Exp.Var (v,_) => 
                  let 
                    val typedvar = RP.make_typedvar (v())
                  in 
                    if flag then (l1,(RP.RRel(c,typedvar))::l2) else ((RP.RVar typedvar)::l1,l2)
                  end
                | Exp.Const f => (case (constexp_to_int e) of
                      SOME i => ((RP.RInt i)::l1,l2)
                    | NONE => (print ("Constructor args error\n");assertfalse())
                  )
                | _ => fail "Constructor args should contain only atoms\n"

              )
              val _ = assertl (conargs,flags,"assertl - conargs,flags\n")
              val (l1,l2) = List.fold2(conargs,flags,([],[]),separate)
              val set = RP.make_runion ((RP.make_rset l1)::l2)
            in
              set
            end)
        | _ => RP.make_dummy_rexpr()
      )
    | _ =>  RP.make_dummy_rexpr()
  
  (* constant to PInt; variable to PVar *)
  fun expression_to_pexpr e =
    case (Exp.node e) of
        (Exp.Const f) => 
          (case (Type.toMyType (Exp.ty e)) of
              Tconstr (t, []) => 
                if (Tycon.isIntX t) then
                  let val constval = f() in
                    case constval of 
                         Const.IntInf n => (Predicate.PInt (IntInf.toInt n))
                   | Const.Word n => (Predicate.PInt (WordX.toInt n))
                   | _ => (print "toPredIntError\n"; assertfalse ())
                  end  		
                else Predicate.PVar (Var.mk_ident "dummy")
            | _ => Predicate.PVar (Var.mk_ident "dummy"))
      | Exp.Var (varf, _) => Predicate.PVar (varf())
      | Exp.App (e1, e2) => (
        case (Exp.node e1, Exp.node e2) of
          (Exp.Var (var, _), _) => 
            let val funname = Var.toString (var())
              val arithops = ["+", "-", "*", "/", "div", "mod"]
              val built_ins = ["length_0", "nRows_0", "nCols_0", "size"]
            in
              if (List.exists (arithops, fn arithop => (String.compare (arithop, funname) = EQUAL))) then (
                let val (expr1, expr2) = case (Exp.node e2) of
                  Exp.Record r => 
                    let val eparam = Vector.toList (Record.toVector r)  
                      val e1 = (fn (a, b) => b) (List.first eparam)
                      val e2 = (fn (a, b) => b) (List.last eparam)
                    in (expression_to_pexpr e1, expression_to_pexpr e2) end
                  | _ => (print "Fail to transform arithmetic operation into predicate logic\n"; assertfalse ())
                in
                  case funname of
                    "+" => Predicate.Binop (expr1, Predicate.Plus, expr2)
                    | "-" => Predicate.Binop (expr1, Predicate.Minus, expr2)
                    | "*" => Predicate.Binop (expr1, Predicate.Times, expr2)
                    | "div" => Predicate.Binop (expr1, Predicate.Div, expr2)
                    | "mod" => Predicate.Binop (expr1, Predicate.Mod, expr2)
                    | "/" => Predicate.Binop (expr1, Predicate.Div, expr2)
                    | _ => (print "Fail to transfrom arithmetic operation into predicate logic\n"; assertfalse ())
                end
              )
              else if (List.exists (built_ins, fn built_in => (String.compare (built_in, funname) = EQUAL))) then  
                Predicate.FunApp (funname, [expression_to_pexpr e2])
              else 
                (* Why dummy?  *)
                Predicate.PVar (Var.mk_ident "dummy")
            end
          | (Exp.Con (c, targs), _) => Predicate.FunApp (Con.toString c, [expression_to_pexpr e2])
          | _ => 
            let val name = getFunctionAppName e
            in
              if (HashTable.inDomain (Builtin.retranslated_name) name) then
                let val param = expression_to_pexpr e2
                  val fapp = expression_to_pexpr e1
                in case fapp of
                  Predicate.FunApp (funname, plist) => Predicate.FunApp (funname, List.append (plist, [param]))
                  | _ => (print ("Program cannot be checked for expression" ^ (CoreML.visitExp e)); assertfalse ())
                end
              else Predicate.PVar (Var.mk_ident "dummy") 
            end
      )
      | Exp.Record r => Predicate.PVar (Var.mk_ident "dummy") 
      | _ => Predicate.PVar (Var.mk_ident "dummy")
  
  fun matchcase_exp_to_pexpr e = (* returns pexpr list *)
    case (Exp.node e) of
        (Exp.Record r) => Vector.toListMap ((Record.range r), fn p => expression_to_pexpr p) 
      | (Exp.Var (varf, _)) => [expression_to_pexpr e]
      | _ => (print ("\nUnspported expression when matchcase " ^ (CoreML.visitExp e) ^ "\n"); assertfalse ())
  
  (* Remember generated frames *)		                           
  val flogs : (string, Frame.t) HashTable.hash_table = HashTable.mkTable (HashString.hashString, (op =)) (101, Not_found)                             
                                  
  (* Remember a frame *)
  fun log_frame exp fr = HashTable.insert flogs (visitExp exp,fr)
  
  fun framemap_apply_solution s = HashTable.map (F.apply_solution s) flogs
  
  fun dump_frames sourcefile flogs =
      let val outfile = TextIO.openAppend ((sourcefile) ^ ".annot") 
      in
        (HashTable.foldi (fn (e, fr, ()) => (TextIO.output(outfile, e); 
                        TextIO.output(outfile, " @.type(@.  "); 
                        TextIO.output(outfile, (Frame.pprint fr));
                          TextIO.output(outfile, "@.)@. \n"))
        ) () flogs;
        TextIO.flushOut (outfile))
    end
       

  fun lcstrs_to_fcstrs (lcstrs : Cs.labeled_constraint list) =
    List.map (lcstrs,
      (fn (Cs.lc lcstr) => #lc_cstr lcstr)
    )

  (* Enclose exp and frame into labeled constraint *)
  (* This function is called from  constrainExp 
     with current belong_pat. Recall that belong_pat is
     updated whenever we are adding a new binding.
     This function is one of the two places where 
     constraints are tagged with belong_pat 
     The other place is constrain_and_bind when
     rhs of binding is a recursive function. *)
  fun label_rconstraint exp rfc = 
    let val og = case (Exp.node exp) of
        Exp.App (e1, e2) => (case (Exp.node e1) of 
                  (Exp.Var (var, targs)) => if (String.compare (Var.toString (var ()), "assert") = EQUAL)
                            then RCs.RAssert exp
                            else RCs.RLoc (SOME exp)
                | _ => RCs.RLoc (SOME exp))
      | _ => RCs.RLoc (SOME exp)
    in 
      RCs.lc {lc_cstr = rfc, lc_orig = og, 
      lc_id = Constraint.fresh_fc_id()}  (* use same id generator *)
    end

  fun label_constraint exp belong_pat fc = 
    let val og = case (Exp.node exp) of
        Exp.App (e1, e2) => (case (Exp.node e1) of 
                  (Exp.Var (var, targs)) => if (String.compare (Var.toString (var ()), "assert") = EQUAL)
                            then Constraint.Assert exp
                            else Constraint.Loc (SOME exp)
                | _ => Constraint.Loc (SOME exp))
      | _ => Constraint.Loc (SOME exp)
    in Constraint.lc {lc_cstr = fc, lc_orig = og, lc_id = Constraint.fresh_fc_id(), lc_binding = belong_pat}  end
	
		(* Find is function is a real recursive function *)
  fun isRecursiveFun bodyExp funvar = 
    let val recflag = ref false
    in
      (Exp.foreachVar (bodyExp, (fn mvar => if Var.logic_equals(mvar, funvar) 
                        then recflag := true 
                        else ())
      ); !recflag)
    end

  fun getConIndex con ty = 
    let val tyc = Type.deConOpt ty
    in
      case tyc of
        SOME (tyc, _) => 
          if (TM.tycon_mem tycon_map tyc) then
            let val con_te_list = TM.get_tycon_def tycon_map tyc
            in
              case (List.index (con_te_list, fn (c, _) => Con.equals (c, con))) of
                SOME index => index
                | NONE => (print "\nCannot find the index of current constructor encoutered in its constructor list\n"; assertfalse ())
            end
          else (* there could be built-in constructors*) if (String.equals (Con.toString con, "::")) then 1
          else (print ("\nCannot get constructors list in which current construnctor encountered is in " ^ (Con.toString con) ^ "\n"); assertfalse ())
        | NONE => (print ("\nCannot get tycon from the constructor's type " ^ (Con.toString con) ^ "\n"); assertfalse ())
    end
   
  fun pat_var pat = case (Pat.node pat) of 
    Pat.Var var => var 
    | Pat.Wild => Var.mk_ident ""
    | _ => (print "\nCannot get variable from given pat\n"; assertfalse ())
    
  fun pat_vars pat = 
    case (Pat.node pat) of 
      Pat.Wild => [Var.mk_ident ""]
      | Pat.Record tr => List.map (Vector.toList (Record.range tr), pat_var)
      | Pat.Tuple ts => if ((Vector.length ts) = 0) then [Var.mk_ident ""] else List.map (Vector.toList ts, pat_var)
      | _ => (print "\nCannot get variables from given pat\n"; assertfalse ())
  
  fun pat_eq (pat1, pat2) = Var.logic_equals (pat_var pat1, pat_var pat2)
  
  (* returns true if exp is 
     1. constructor application
     2, assertfalse, or
     3. a variable
   *)
  fun is_poly_instantiation exp = 
    case exp of
       Exp.App (e1, e2) => (case (Exp.node e1) of
                      (Exp.Con (c, targs)) => true
                    | (Exp.Var (var, targs)) => (String.compare (Var.toString (var ()), "assertfalse") = EQUAL)
                    | _ => false)
          | Exp.Var (var, targs) => true
          | _ => false

  (* returns true if the expty is a basic type or exp is assertfalse*)
  fun is_not_relation exp ty = case (exp, ty) of
      (_,Tconstr(tycon,tyargs)) => not (TM.tycon_mem tycon_map tycon)
    | (Exp.App(e1,e2),_) => (case Exp.node e1 of 
          Exp.Var (var,_) => (String.compare (Var.toString (var ()), "assertfalse") = EQUAL)
        | _ => false)
    | _ => false
  
  (* Creates a new frame for given expression of given type. *)
  (* desc is Exp.t. ty is Type_desc.t. *)
  fun expr_fresh desc ty = 
    if is_poly_instantiation desc then 
      (* unconstrained frame has Bottom refinement. *)
      Frame.fresh_unconstrained ty tycon_map
    else 
      Frame.fresh ty tycon_map

  fun rexpr_fresh desc ty = 
    if (is_not_relation desc ty) then 
      RF.fresh_unconstrained ty tycon_map
    else 
      RF.fresh ty tycon_map
          
  (* lm as Lam {arg, argType, body = Exp {ty = bodyType, ...}, ...} *)
  (*
   *@param cstrs is the labeled_constraint
   *@param binding_table is the (pat, exp) binding definition table
   *@param call_deps is the (pat, pat) call dependencies list
   *@param binding_frame is the (pat, frame) binding frame definition table
   *@param paths is the path encoding of the program
   *@return a tuple of (fenv, cstrs, binding_table, call_deps, binding_frame)
   *)
  fun constrain_structure initfenv initrenv guard pdecs (polymatching_table : (Var.t,Var.t) HashTable.hash_table) =
    let 
      fun constrain_rec fenv renv guard cstrs rstrs pdecs =
        let
          fun binder {lambda=lm, var=var'} = 
            let
              val lm' = Lambda.dest lm
              val argType = #argType lm'
              val body = #body lm'
              val bodyType = Exp.ty body
              val fpat = (Pat.var (var', Type.arrow (argType, bodyType)))
              val rec_flag = isRecursiveFun body var'
            in
              ((fpat, (Exp.lambda lm)),rec_flag)
            end
        in
          case pdecs of 
            [] => (fenv, renv, cstrs, rstrs) 
          | (Dec.Datatype v) :: pdecs' => 
                let val _ = TM.bind_datatypes tycon_map v in
                  constrain_rec fenv renv guard cstrs rstrs pdecs'
                end
          | (Dec.Exception ca) :: pdecs' => constrain_rec fenv renv guard cstrs rstrs pdecs' 
          | (Dec.Fun {decs, tyvars, ...}) :: pdecs' => 
              let
                val	(bindings,rec_flags) = List.unzip (Vector.toListMap (decs, binder))
                val rec_flag = case rec_flags of f::[] => f | _ => true (* More decs => mutually recursive functions *)
                val (fenv, renv, cstrs', rstrs') 
                    = constrain_bindings fenv renv guard rec_flag bindings polymatching_table
              in
                constrain_rec fenv renv guard (cstrs @ cstrs') (rstrs @ rstrs') pdecs'
              end
          | (Dec.Val {rvbs, tyvars, vbs, ...}) :: pdecs' =>
              let
                (* simplifying assumption : all val rec bindings are recursive *)
                val	rec_bindings = List.map
                    (Vector.toListMap (rvbs, binder),fst)
                val (fenv, renv, cstrs1', rstrs1') = constrain_bindings fenv renv guard true rec_bindings polymatching_table
                val bindings = (Vector.toListMap (vbs, (fn {exp=exp', pat=pat', ...} => ( (pat', exp')))))
                val (fenv, renv, cstrs2', rstrs2') = constrain_bindings fenv renv guard false bindings polymatching_table
              in 
                constrain_rec fenv renv guard (cstrs @ cstrs1' @ cstrs2') (rstrs @ rstrs1' @ rstrs2') pdecs' 
              end
        end
      (*end of constrain_rec*)
      val (fenv,renv,cstrs,rstrs) =constrain_rec initfenv initrenv guard [] [] pdecs  
    in 
      (fenv,renv,cstrs,rstrs,tycon_map)
    end
      
  and constrain_bindings env renv guard recflag bindings polymatching_table =
    case recflag of (* return Le.t*(Constraint.labeled_constraint list) *)
      false => List.fold (
                  bindings, (* Pat.t*Exp.t list *)
                  (env, renv,[] ,[]), 
                  (constrain_and_bind guard polymatching_table)
               )
    | true =>
      let 
        val exprs = List.map (bindings, (fn (a, b) => b))
        val pats = List.map (bindings, (fn (a, b) => a))
        val fbindings = List.map (bindings, (fn (p, e) => (p, e, expression_to_pexpr e)))
        val rbindings = List.map (bindings, (fn (p, e) => (p, e, expression_to_rexpr e)))
        val unlabeled_frames = List.map (exprs, (fn e => F.fresh (Type.toMyType (Exp.ty e)) tycon_map))
        val unlabeled_rframes = List.map (exprs, (fn e => RF.fresh (Type.toMyType (Exp.ty e)) tycon_map))
        val unlabeled_env = bind_all fbindings unlabeled_frames env
        val unlabeled_renv = rbind_all rbindings unlabeled_rframes renv
        val (label_frames,label_rframes,_,_) = constrain_subexprs unlabeled_env unlabeled_renv 
                                                   guard exprs polymatching_table
        val _  = assertl (unlabeled_rframes, label_rframes, "assertl - unlabeled_rframes, label_rframes")
        val _  = assertl (unlabeled_frames, label_frames, "assertl - unlabeled_frames, label_frames")
        (*val binding_frames = List.map2 (unlabeled_frames, label_frames, (fn (a, b) => F.label_like a b)) *)
        val binding_frames = label_frames (* TO BE REMOVED *)
        val binding_rframes = List.map2 (unlabeled_rframes, label_rframes, (fn (a, b) => RF.label_like a b)) 
        (* Redo constraints now that we know what the right labels are *)
        val bound_env = bind_all fbindings binding_frames env
        val bound_renv = rbind_all rbindings binding_rframes renv
        val bound_rel_env = (bound_env,bound_renv,guard)
        val (found_frames, found_rframes, subexp_cstrs, subexp_rstrs) = 
            constrain_subexprs bound_env bound_renv guard exprs polymatching_table	

        fun make_cstr fc pat = Cs.lc {lc_cstr = fc, lc_orig = Cs.Loc NONE, lc_id = Cs.fresh_fc_id (), lc_binding = pat}
        fun make_rstr fc pat = RCs.lc {lc_cstr = fc, lc_orig = RCs.RLoc NONE, lc_id = Cs.fresh_fc_id ()}
        fun build_found_frame_cstr_list (found_frame, binding_f, pat, cs) =
            make_cstr (Cs.WFFrame (bound_env, binding_f)) pat ::
            make_cstr (Cs.SubFrame (bound_env, guard, found_frame, binding_f)) pat :: cs
        fun build_found_frame_rstr_list (found_rframe, binding_rf, pat, rcs) =
            make_rstr (RCs.WFRFrame (bound_rel_env, binding_rf)) pat ::
            make_rstr (RCs.SubRFrame (bound_rel_env, found_rframe, binding_rf)) pat :: rcs
      in 
        (bound_env, bound_renv, 
        (List.fold3 (found_frames, binding_frames, pats, [], build_found_frame_cstr_list)) @ subexp_cstrs,
        (List.fold3 (found_rframes, binding_rframes, pats, [], build_found_frame_rstr_list)) @ subexp_rstrs) 
      end
  
  (*
   * If pexpr is a function call, and pat is a tuple/record, we name a distinct variable for this pat. And bing it in the env.
   *)
  and tbind env pat frame pexpr =
    let 
      val _ = print ("PatBind: "^(CoreML.Pat.visitPat pat)^" with \n"^
        "[F] "^(F.pprint frame)^"\n"^
        "[Pexpr] "^(P.pprint_pexpr pexpr)^"\n")
      val env = (*case (Pat.node pat, frame, pexpr) of (* A little sanity *)
            (Pat.Tuple _, Frame.Frecord _, Predicate.PVar record_var) => Le.env_bind_record env pat frame record_var
            | _ =>*) Le.new_env_bind env pat frame tycon_map
    in
      (* everything except wild and var is deep *)
      if Pattern.is_deep pat then
          Le.add (Var.mk_ident "pattern")
            (B.mk_int [(Var.mk_ident "", Var.mk_ident "", Pattern.desugar_bind pat pexpr)])
            env
        else env
    end

  and rbind renv pat rframe rexpr =
  let
    val renv = RLe.env_bind renv pat rframe rexpr tycon_map
    val _ = print ("PatRelBind: "^(CoreML.Pat.visitPat pat)^" with \n"^
      "[RF] "^(RF.pprint rframe)^"\n"^
      "[Rexpr] "^(RP.pprint_rexpr rexpr)^"\n")
  in
    if (Pattern.is_deep pat) then
      RLe.add (Var.mk_ident "pattern")
        (RB.mk_poly [(Var.mk_ident "pat", Var.mk_ident "pat", 
          Pattern.desugar_rbind pat rexpr tycon_map)])
        renv
    else
      renv
  end

  (*
   * frame and pexprs are all for the test, while pat is for pattern which should match to the given test
   *)	
  and matchcase_tbind env pat frame pexprs = 
    let 
      (* 
       * we are binding current patten with test's frame. 
       * So, (x,y) pat is bound to {v|v.1=x0 /\ v.2=x1}  
       *)
      val env = Le.new_env_bind env pat frame tycon_map
    in
      if Pattern.is_deep pat then (
        case (Pat.node pat) of 
          (Pat.Tuple pats) => (
            (*List.foreach (pexprs, fn pexpr => print ((Predicate.pprint_pexpr pexpr) ^ "\n"));
            List.foreach ((Vector.toList pats), fn pat => print ((CoreML.Pat.visitPat pat) ^ "\n"));*)

            (* Now bind all pats inside current pat to corresponding pexprs *)
            if (Vector.length pats = List.length pexprs) then
              List.fold2 ((Vector.toList pats), pexprs, env, (fn (pat, pexpr, env') => 
                      Le.add (Var.mk_ident "pattern")
                      (B.mk_int [(Var.mk_ident "", Var.mk_ident "", Pattern.desugar_bind pat pexpr)])
                      env'
                      ))
            else (
              List.foreach (pexprs, fn pexpr => print ("impossible checking failure " ^ (Predicate.pprint_pexpr pexpr) ^ "\n"));
              assertfalse ()
            )	
            )
          | (Pat.Con {arg, con, targs}) => 
            Le.add (Var.mk_ident "constructor")
            (B.mk_int [(Var.mk_ident "", Var.mk_ident "", 
              Predicate.Atom (Predicate.FunApp ("__constr", pexprs), Predicate.Eq, 
              (Predicate.PInt (getConIndex con (CoreML.Pat.ty pat)))))])
            env
          | Pat.List _ => env
          | _ => (print ("\nUnknow pattern mathcing " ^ (CoreML.Pat.visitPat pat) ^ "\n"); assertfalse ()))
      else env
    end
      
  (* TODO: replace lightenv implementation with applicative map. Hashtable is ridiculous *)
  and constrain_and_bind guard polymatching_table ((pat, e), (env, renv, cstrs, rstrs)) =
    let 
      val _ = (print "binding ... pat is "; print (CoreML.Pat.visitPat pat); print " exp is "; print (CoreML.visitExp e))
      val env_copy = Le.copy env
      val renv_copy = RLe.copy renv
      val (f, rf, cstrs',rstrs') = constrainExp e env_copy renv_copy guard polymatching_table
      val rexpr = expression_to_rexpr e
      val pexpr = expression_to_pexpr e
      val env = tbind env pat f pexpr
      val renv = rbind renv pat rf rexpr
    in 
      (env, renv, cstrs @ cstrs', rstrs @ rstrs')
    end
  
  and bind_all bindings fs env = List.foldr2 (bindings, fs, env, (fn ((p, e, px), f, env) => tbind env p f px))

  and rbind_all bindings rfs renv = 
    List.foldr2 (bindings, rfs, renv, (fn ((p, e, rx), rf, renv) => rbind renv p rf rx))
  
  and constrain_subexprs env renv guard es polymatching_table = 
      List.foldr (es, ([], [], [], []), (fn (e, (fs, rfs, cs, rcs)) 
        => let val (f, rf, cs', rcs') = constrainExp e env renv guard polymatching_table 
            in (f :: fs, rf::rfs, cs' @ cs, rcs' @ rcs) end))

  and constrain_nullary_constructed expty rf = case rf of
      RF.RFconstr(tycon,tyargfs,_) => 
      if(TM.tycon_mem tycon_map tycon) then
        let
          val rexp = RP.make_null_rset ()
          val qual = RQ.equality_qualifier defaultCons rexp
          val refn = RF.fresh_refinement qual
        in
          RF.RFconstr(tycon,tyargfs,refn)
        end
      else
        (* if tycon not in table, then rf already should have empty refinement *)
        rf
    | _ => fail("Non constr frame for type constructor\n")

  and constrainExp e env renv guard polymatching_table = 
  let 
    val _ = print ("Constraining Exp " ^ (CoreML.visitExp e) ^ "\n")
    val desc= (Exp.node e)
    val tyy = type_desc e
    (* lo and behold, for a new frame is born! *)
    val environment = (env, guard, expr_fresh desc tyy)
    val renvironment = (renv, guard, rexpr_fresh desc tyy)
    val (f, rf, cstrs, rstrs, rec_cstrs, rec_rstrs) = case desc of
        Exp.Const f =>
        let 
          val(f,rf) =  constrain_constant (f())
        in
          (f,rf,[],[],[],[])
        end
      | Exp.Con (c, targs) => (* case of unary constructors being rhs of binding *)
          let
            val (f,rf) = (case (Con.toString c) of
                "true" => (F.Fconstr (Tycon.bool, [], Frame.fresh_true ()), RB.uBool)
              | "false" => (F.Fconstr (Tycon.bool, [], Frame.false_refinement), RB.uBool) 
              |_  => (#3 environment, (constrain_nullary_constructed tyy (#3 renvironment))))
          in
            (f, rf,[],[],[], [])
          end
      | Exp.Record r => constrain_record environment renvironment (Record.toVector(r)) polymatching_table
      | Exp.Case {rules, test, ...} => 
        let
          val rlist = Vector.toListMap (rules, (fn {exp, pat, ...} => (pat, exp)))
        in
          constrain_match environment renvironment test rlist polymatching_table
        end 
      | Exp.Var (var, targs) => constrain_identifier environment renvironment (var()) e polymatching_table   
      | Exp.App (e1, e2) => (case (Exp.node e1) of 
          (Exp.Con (c, targs)) => 
          let
            val e2list = filter_conargs e2
            val tycon1 = case tyy of Type_desc.Tconstr (tyc, _) => tyc | _ => fail "\nIll constructor\n"
            val tylist = List.map (TM.get_argtys_by_cstr tycon_map c handle Not_found => [],fst)
            val t = Tconstr (tycon1, tylist)
            val sumf = #3 environment
            (*val f = case sumf of
                F.Fsum (_, fs, _) => 
                let val f = List.peek (fs, fn (c', f) => Con.equals (c, c'))
                  val f =  case f of SOME (_,f) => f | NONE => (print "\nIll type from a datatype\n"; assertfalse ())
                in Frame.unfoldRecursiveFrame f tycon1 fs end
              | F.Fconstr (tcc, fls, r) => 
                if (String.equals ("::", Con.toString c)) then F.Fconstr (tcc, (List.first fls :: fls), r) (* This is considered as unsafe *)
                else sumf
              | _ => (print "\nIll sum type from a datatype\n"; assertfalse ())*)
            val rf = #3 renvironment
          in
            constrain_constructed (env, guard, sumf) (renv, guard, rf) e t e2list polymatching_table
          end
        | (Exp.Var (var, targs)) => 
          let
            val rf = #3 renvironment
            val resopt = 
              if (String.compare (Var.toString (var ()), "assert") = EQUAL) then
                SOME (constrain_assert environment renvironment e2 polymatching_table)
              else if (String.compare (Var.toString (var ()), "assertfalse") = EQUAL) then
                SOME (constrain_assertfalse environment renvironment)
              else if (String.compare (Var.toString (var ()), "&&") = EQUAL orelse 
                   String.compare (Var.toString (var ()), "||") = EQUAL ) then
                case (Exp.node e2) of
                  Exp.Record e2 =>
                    let val funname = Var.toString (var ())
                      val lr = Vector.toListMap ((Record.toVector e2), (fn (a, b) => b))
                      val l = List.first lr
                      val r = List.last lr
                      val (fl,_, cstr1,_) = constrainExp l env renv guard polymatching_table
                      val (fr,_,cstr2,_) = constrainExp r env renv guard polymatching_table
                      val pl = case fl of 
                          F.Fconstr (a, b, (subs,F.Qconst[(v1,v2,P.Iff (v3,p))])) => 
                        if Predicate.logic_equals_pexp v3 (B.tag (P.PVar v2)) then 
                          (Predicate.apply_substs subs p)
                        else (print "Error: assert unknown frame encountered."; assertfalse ())
                        | _ => (print "Error: assertion ill formed "; print (Frame.pprint fl); assertfalse ())
                      val pr = case fr of 
                        F.Fconstr (a, b, (subs,F.Qconst[(v1,v2,P.Iff (v3,p))])) => 
                          if Predicate.logic_equals_pexp v3 (B.tag (P.PVar v2)) then 
                             (Predicate.apply_substs subs p)
                          else (print "Error: assert unknown frame encountered."; assertfalse ())
                        | _ => (print "Error: assertion ill formed "; print (Frame.pprint fr); assertfalse ())
                    in
                      if (String.equals (funname, "&&")) then
                        SOME (Builtin.and_frame pl pr, rf, [], [], cstr1 @ cstr2, [])
                      else
                        SOME (Builtin.or_frame pl pr, rf, [], [], cstr1 @ cstr2, [])
                    end
                  | _ => (print "\nassertion && || syntax ill-formed\n"; assertfalse ())	
              else if (String.compare (Var.toString (var ()), "not") = EQUAL) then
                let val (f,_,cstr,_) = constrainExp e2 env renv guard polymatching_table
                  val p = case f of 
                    F.Fconstr (a, b, (subs,F.Qconst[(v1,v2,P.Iff (v3,p))])) => 
                    if Predicate.logic_equals_pexp v3 (B.tag (P.PVar v2)) then 
                      (Predicate.apply_substs subs p)
                    else (print "Error: not unknown frame encountered in not app."; assertfalse ())
                  | F.Fconstr (a, b, (subs, F.Qconst[(v1,v2,P.Atom (v3, P.Eq, bf))])) =>
                    if (Predicate.logic_equals_pexp v3 (P.PVar v2)) then
                      (P.Iff (bf, P.True))
                    else (print "Error: not unknown frame with boolean expression."; assertfalse ())
                  | _ => (print "Error: assertion ill formed in not app"; print (Frame.pprint f); assertfalse ())
                in
                  SOME (Builtin.not_frame p, rf, [], [], cstr, [])
                end
              else NONE
          in
            (case resopt of
                SOME p  => p
              | NONE => constrain_application environment renvironment e1 e2 polymatching_table)
          end
        | _ => constrain_application environment renvironment e1 e2 polymatching_table)
      | Exp.Let (ds, e) => constrain_let environment renvironment (Vector.toList ds) e polymatching_table
      | Exp.List es => fail "List expression encountered\n"
      | Exp.Seq es => constrain_sequence environment renvironment es polymatching_table
      | Exp.Lambda l => constrain_lambda environment renvironment l 
                                          polymatching_table
      | Exp.EnterLeave (e, si) => fail "We do not check EnterLeave"
      | Exp.Handle {catch, handler, try} => fail "We don not check Handle"
      | Exp.PrimApp {args, prim, targs} => fail "We do not check PrimApp"
      | Exp.Raise e => fail "We do not check Raise"
      | _ => fail "unexpected expression\n"
    in 
      let
        val dummy_pat = Pat.var (Var.fromString "dummymain", 
          Type.var(Tyvar.newNoname {equality = false}))
        val lcstrs = List.map (cstrs, (label_constraint e dummy_pat))
        val lrstrs = List.map (rstrs, (label_rconstraint e))
      in
        log_frame e f; 
        (f, rf, lcstrs @ rec_cstrs, lrstrs @ rec_rstrs)
      end
    end
  
  (* rframes for constants are frames with no refinement *)
  and constrain_constant cons = (case cons of 
         Const.IntInf n => 
         let
          val rf = RB.uInt
          val f = B.mk_int [B.equality_qualifier (P.PInt (IntInf.toInt n))]
         in
          (f,rf)
         end
       | Const.Null => (B.uUnit, RB.uUnit)
       | Const.Real _ => (B.uFloat, RB.uFloat)
       | Const.Word n => 
          (B.mk_int [B.equality_qualifier (P.PInt (IntInf.toInt (WordX.toIntInfX n)))], RB.uInt)
       | Const.WordVector _ => fail "Can't constrain wordvector constant\n"
     )
  
  (* 
   * By constructor here, we temporarily do not consider constructor for list or array.
   * Parameter cstrdesc is the type of the constructor
   * Parameter args is the parameters of this constructor
   *)
  and constrain_constructed (env, guard, f) (renv,_,rf) e cstrdesc args polymatching_table =
    case f of
      F.Fconstr (path, tyargframes, refn) =>
        let 
          val c = case Exp.node e of Exp.App(e1,e2) => (case Exp.node e1 of
                Exp.Con(c',_) => c' | _ => fail "Not a constructor application\n")
            | _ => fail "Not even an application\n"
          val tyargfs = case rf of RF.RFconstr (_,fs,_) => fs | _ => fail "RFconstr expected\n"
          val rexpr = expression_to_rexpr e
          val argsupfs = RF.fresh_constructor c tyargfs rexpr tycon_map
          val argsupframes = F.fresh_constructor c f tycon_map
          val refn = RF.fresh_refinement (RQ.equality_qualifier c rexpr)
          val rf' = case rf of RF.RFconstr (p,fs,_) => RF.RFconstr (p,fs,refn) | _ => fail ""
          val _ = print "go here0\n"
          val (argsubframes,argsubfs,argcstrs,argrstrs) = 
            constrain_subexprs env renv guard args polymatching_table
          val _ = print "go here\n"
          val rel_env = (env,renv,guard)
          val _ = assertl (argsubfs,argsupfs,"assertl - argsubfs,argsupfs")
          val rstrs = RCs.WFRFrame (rel_env,rf)::
            RCs.WFRFrame (rel_env,rf')::
            RCs.SubRFrame(rel_env,rf',rf)::
            (List.map (argsupfs,
            (fn(rsup)=>RCs.WFRFrame(rel_env,rsup))))@
            (List.map2 (argsubfs,argsupfs,
            (fn (rsub,rsup) => RCs.SubRFrame(rel_env,rsub,rsup))))
          val cstrs = Cs.WFFrame(env, f) :: 
            (List.map2 (argsupframes, argsubframes,
            (fn (arg, formal) => Cs.SubFrame(env, guard, arg, formal))))
        in
            (* this should fail *)
            (* cstr args are frames for tyargs of current type *)
            (* argframes are frames of args of valcon. *)
            (* subtyping among them isn't meaningful *)
            (f,rf,cstrs,rstrs,argcstrs,argrstrs) 
         end
        | _ => fail "Fconstr expected\n"
  
  and is_sum_type ty = case ty of
      Tconstr(tycon,tyargs) => TM.tycon_mem tycon_map tycon
    | _ => false

  (* In this function, we first get the expression of all recored fields.
   * Then we constrain this field expression
   * Then we build refinements for this fiel expression
   * Then we add subtyping contraints mainly for actual <: formal
   *)
  and constrain_record (env, guard, f) (renv, rguard, rf) labeled_exprs polymatching_table =
    let
        val labeled_exprs = QuickSort.sortVector ( 
                              labeled_exprs, 
                              (fn ((a, b), (a', b'))=> (Field.<= (a, a')))
                            )	 
        val sorted_exprs = ((Vector.toList o (fn (a, b) => b)) (Vector.unzip labeled_exprs))
        val (subframes, subrframes, subexp_cs, subexp_rcs) = 
            constrain_subexprs env renv guard sorted_exprs polymatching_table
        (* Individual frames for record fields must match 
           corresponding frames of sub-expressions *)
        fun subframe_field (fsub, (fsup, _), cs_rest) = (Cs.SubFrame (env, guard, fsub, fsup)) :: cs_rest 
        fun subrframe_field rel_env (rfsub, (rfsup,_),rcs_rest) = 
          (RCs.SubRFrame (rel_env,rfsub,rfsup)) :: rcs_rest
        val (ret_f, cur_cs) = case f of
            F.Frecord (recframes, _) => 
              let 
                fun field_qualifier ((_, name), fexpr) = B.field_eq_qualifier name (expression_to_pexpr fexpr) 
                (* In case of tuples, names are "1", "2".. So, qualifier would
                   be x11.1 = pfexp1, x11.2 = pfexp2...*)
                val ret_f = F.Frecord (recframes, ([], F.Qconst (List.map2 (recframes, sorted_exprs, field_qualifier))))
                val _ = assertl (subframes, recframes, "assertl:subframes-recframes\n")
                val (cur_cs : Cs.frame_constraint list) = Cs.WFFrame (env, f) :: List.fold2 (subframes, recframes, [], subframe_field)
                val (slist : Cs.frame_constraint list) = lcstrs_to_fcstrs subexp_cs
                val ret_cs = cur_cs@slist
              in
                (ret_f, cur_cs)
              end
            | _ => fail ("Expected record frame\n")
        val (ret_rf, cur_rcs) = case rf of
            RF.RFrecord (recrframes, _) => 
              let 
                (*fun field_rqualifier_list ((_, name), fexpr) acc = 
                let
                  val ftype = type_desc fexpr
                in
                  if (is_sum_type ftype) then 
                    (RB.field_eq_qualifier name defaultCons (expression_to_rexpr fexpr))::acc
                  else
                    acc
                end
                val _ = assertl (recframes,sorted_exprs,"assertl - recframes,sorted_exprs\n")
                val ref_rquals = List.fold2(recframes,sorted_exprs,[],field_rqualifier_list)
                val refn = if(List.length ref_rquals > 0) 
                  then ([],RF.RQconst ref_rquals) 
                  else RF.fresh_refinementvar RF.RBottom*)
                (* CURRENTLY IGNORING RECORDS *)
                (* To handle records, relem should include pexprs *)
                val refn = RF.empty_refinement
                val ret_rf = RF.RFrecord (recrframes,refn)
                val rel_env = (env,renv,guard)
                (*val _ = assertl (recrframes,subrframes,"assertl - recrframes,subrframes\n")*)
                (*val (cur_rcs : RCs.rframe_constraint list) = 
                  RCs.WFRFrame (rel_env, rf) :: List.fold2 (subrframes, recrframes, [], subrframe_field rel_env)*)
                val cur_rcs = []
              in
                (ret_rf, cur_rcs)
              end
            | _ => fail ("Expected record rframe\n")
    in
      (ret_f,ret_rf,cur_cs,cur_rcs,subexp_cs,subexp_rcs)
     end
     
      
  (* matchf is the frame of the test condition while matche is the Predicate.pexpr ofthe test condition *)
  and constrain_case environment renvironment matchf matchrf 
                      match_pexpr (* pexpr list *)
                      match_rexpr
                      polymatching_table 
                      (guardvar, i, (pat, e)) =
    let 
      val (env,guard,f) = environment
      val (renv,_,rf) = renvironment
      (* guard updated with correct guard value *)
      val guard = (guardvar, i, true) :: guard
      val env = tbind env pat matchf match_pexpr
      (* Now, env contains mapping bewteen  
         1. pat frame and matchf
         2. forevery pat' inside pat and
              for corresponding pexpr' inside matche
                pat' -> pexpr'
       *)
      val renv = rbind renv pat matchrf match_rexpr (*again, no spl treatment*)
      val (fe, rfe, subcs, subrcs) = constrainExp e env renv guard polymatching_table
      (* generated constraints refer to extended env and updated guard *)
      val ret_cs = (Cs.SubFrame (env, guard, fe, f))::(lcstrs_to_fcstrs subcs)
      val rel_env = (env,renv,guard)
    in 
      (Cs.SubFrame (env, guard, fe, f), RCs.SubRFrame (rel_env,rfe,rf), subcs, subrcs) 
    end
  
  (* e is the test; pexps are paris of (pat, exp) *)
  and constrain_match (environment as (env, guard, f)) 
                      (renvironment as (renv,_,rf))
                      e (* this is test *)
                      pexps (* (pat,expr) list *)
                      polymatching_table =
    if (Type.isBool (Exp.ty e)) then
      let 
        val _ = print ("Constaining bool expression : "^(CoreML.visitExp e)^"\n")
        val (f1, rf1, cstrs1, rstrs1) = constrainExp e env renv guard polymatching_table
        (* guardvar creation site. we have 2 cases *)
        val guardvar = Var.mk_ident "guard"
        val (f1, guard2, guard3) = case f1 of 
            (* v1 : ">=", v2 : Var(z), v3 : pexpr *)
            F.Fconstr (a, b, (subs,F.Qconst[(v1,v2,P.Iff (v3,p))])) => 
              (f1, (guardvar, 1, true) :: guard, (guardvar, 0, true) :: guard)
          | F.Fconstr (a, b, (subs, F.Qconst [(v1, v2, P.Atom (v3, P.Eq, bf))])) => 
            let 
              val pd = P.big_and [P.Atom (v3, P.Eq, bf), P.Atom (v3, P.Lt, P.PInt 2), P.Atom (v3, P.Ge, P.PInt 0)]
            in 
              (F.Fconstr (a, b, (subs, F.Qconst [(v1, v2, pd)])), (guardvar, 1, false) :: guard, (guardvar, 0, false) :: guard) 
            end
          | _ => (print ("Error: if-then-else branching condition ill formed" ^ (Frame.pprint f1)); assertfalse ())	
          
        (* We extend the environment with the frame of bool test 
           We create a guardvar g and associate the frame to g. So env contains g -> f
           guard_t array associates g to an integer describing current case.
         *)
        val env' = Le.add guardvar f1 env 
            (* fli : frame for entire case-rules, cli - constraons for entire case-rules *)		
        val (subflist, subrflist, subclist, subrclist) = 
          List.fold (pexps, ([], [], [], []), (fn ((p, e), (fli, rfli, cli, rli)) => case (Pat.node p) of 
              Pat.Con {arg=arg',con=con',targs=targs'} => 
              let
                val grd' = (case Con.toString (con') of
                    "true" => guard2
                  | "false" => guard3
                  | _ => fail "bool cons not in true|false\n"
                )
                val (f', rf', cstrs', rstrs') = constrainExp e env' renv grd' polymatching_table
                val rel_env = (env',renv,grd')
                val subflist = Cs.SubFrame(env',grd', f', f) :: fli
                val subrflist = RCs.SubRFrame (rel_env,rf', rf) :: rfli
              in
                (subflist,subrflist,cstrs'@cli,rstrs'@rli)
              end
            | _ =>(print "if-then-else error1\n";assertfalse())))
        val rel_env = (env',renv,guard)
      in
        (f, rf, Cs.WFFrame(env, f) :: subflist, (RCs.WFRFrame(rel_env,rf))::subrflist,cstrs1 @ subclist, rstrs1@subrclist)
      end
    else 
      (* not a boolean expression *)
      let 
        (* frame and cstrs for case test expr *)
        val (matchf, matchrf, matchcstrs, matchrstrs) = 
          constrainExp e env renv guard polymatching_table
        val cases_size = List.length pexps
        val v1 = Var.mk_ident ""
        val v2 = Var.mk_ident "" 
        val p1 = P.Atom (B.tag (P.PVar v2), P.Lt, (P.PInt cases_size)) 
        val p2 = P.Atom (B.tag (P.PVar v2), P.Ge, (P.PInt 0)) 
        val q = (v1, v2, P.And (p1, p2))
        (* Only Integer type constr *)
        val f1 = F.Fconstr(Tycon.defaultInt (), [], ([], F.Qconst [q]))
        (* Here comes the guardvar *)
        (* guardvar is int-tagged to enumerate cases *)
        val guardvar = Var.mk_ident "guard"
        (* env is extended with (guardvar -> test_frame) mapping *)
        val env' = Le.add guardvar f1 env
        val environment = (env', guard, f)
        val test_pexpr = expression_to_pexpr e
        val test_rexpr = expression_to_rexpr e (* no spl treatment*)
        val cases = List.mapi (pexps, fn (i, (pat, e')) => 
            (constrain_case environment renvironment matchf matchrf test_pexpr test_rexpr polymatching_table 
                                                                            (guardvar, i, (pat, e'))))
                                                                                  val rel_env = (env',renv,guard)
        val cstrs = List.map (cases, (fn (a, b, c, d) => a))
        val rstrs = List.map (cases, (fn (a, b, c, d) => b))
        val subcstrs = List.map (cases, (fn (a, b, c, d) => c))
        val subrstrs = List.map (cases, (fn (a, b, c, d) => d))
      in 
        (f, rf, Cs.WFFrame (env, f) :: cstrs, 
        RCs.WFRFrame (rel_env, rf) :: rstrs, 
        List.concat (matchcstrs :: subcstrs),
        List.concat (matchrstrs :: subrstrs)) 
      end
  
  and constrain_lambda (env, guard, f) (renv,_,rf) lam 
                        polymatching_table = (
    let val (pat, e') = (fn {arg=arg', argType=argType', body=body', mayInline=mayInline'} 
      => ((Pat.var (arg', argType')), body')) (Lambda.dest lam)
      in case (f,rf) of
          (F.Farrow (_, f, unlabelled_f'),RF.RFarrow (_,rf,unlabelled_rf')) =>
            (* \pat.e --> Gamme;guard;pat:f |- e:?? *)
            let val env' = Le.new_env_bind env pat f tycon_map
            val renv' = RLe.env_bind renv pat rf 
              (expression_to_rexpr e') tycon_map
            val (f'', rf'',cstrs,rstrs) = constrainExp e' env' renv' guard 
                                            polymatching_table
            val f' = F.label_like unlabelled_f' f''
            val rf' = RF.label_like unlabelled_rf' rf''
            val f = F.Farrow (SOME pat, f, f')
            val rf = RF.RFarrow (SOME pat, rf, rf')
            val (rel_env,rel_env') = ((env,renv,guard),(env',renv',guard))
          in
            (f, rf,
            [Cs.WFFrame (env, f), Cs.SubFrame (env', guard, f'', f')], 
            [RCs.WFRFrame (rel_env, rf), RCs.SubRFrame (rel_env', rf'', rf')], 
            cstrs,
            rstrs)
          end
      | _ => fail "Farrow and RFarrow expected\n"
    end)

  and instantiate_id id f rf env renv e polymatching_table = (
    print ("instantiate_id " ^ (Var.toString id) ^ "...\n");
    let 
      val env_f =
      (Le.find id env) handle Not_found => (
        (let 
           val tyy = Type.toMyType (Exp.ty e)
         in Frame.fresh_without_vars tyy tycon_map end))
      val env_rf = (RLe.find id renv) handle Not_found => (
        let 
           val tyy = Type.toMyType (Exp.ty e)
         in RF.fresh_without_vars tyy tycon_map end)
      val _ = print ("env_f is " ^ (Frame.pprint env_f) ^ "\n")
      val _ = print ("env_rf is " ^ (RF.pprint env_rf) ^ "\n")
      val _ = print "instantiating...\n"
      val new_f = F.instantiate env_f f polymatching_table
      val new_rf = RF.instantiate env_rf rf 
      val _ = print ("Instantiated F is "^(Frame.pprint new_f)^"\n")
      val _ = print ("Instantiation RF is "^(RF.pprint new_rf)^"\n")
    in 
      (new_f,new_rf)
    end)
    
    (* responsible for looking up constraints for existing identifiers  and instantiating them *)
    and constrain_identifier (env, guard, f) (renv,_,rf) id e polymatching_table = 
    let
      val rel_env = (env,renv,guard)
      fun inst_and_refine () =
        let 
          val refn =
            if Le.mem id env then 
              B.equality_refinement (expression_to_pexpr e) 
            else F.empty_refinement
          val r_refn =
            if RLe.mem id renv then 
              RB.equality_refinement defaultCons (expression_to_rexpr e) 
            else RF.empty_refinement (* Notice that refinement changed from RTop to empty *)
            val (inst_f,inst_rf) = instantiate_id id f rf env renv e polymatching_table
          val nf = F.apply_refinement refn inst_f
          val rnf = RF.apply_refinement r_refn inst_rf
        in 
          (nf,rnf,[Cs.WFFrame(env,nf)],[RCs.WFRFrame(rel_env,rnf)],[],[])
        end
      fun inst_only () =
        let
          val (inst_f,inst_rf) = instantiate_id id f rf env renv e polymatching_table
        in
          (inst_f,inst_rf,[Cs.WFFrame(env,inst_f)],[RCs.WFRFrame(rel_env,inst_rf)],[],[])
        end
    in
      case (Type.toMyType (Exp.ty e)) of
        Type_desc.Tconstr _ => (* Based Identifier *) inst_and_refine()
      | Type_desc.Tvar _ => (* Equality over Tvar. Hmm.. *) inst_and_refine()
      | _ => inst_only()
    end
  
  and apply_once env renv guard e2 f rf subexp_cstrs subexp_rstrs 
                 polymatching_table 
                 func = 
    case (f, rf) of
        (F.Farrow (l, f, f'), RF.RFarrow(_,rf,rf')) =>
          let 
            val (f2, rf2, e2_cstrs, e2_rstrs) = constrainExp e2 env renv guard polymatching_table
            val (pexpr,relemlist) = (case (Exp.node e2) of
              Exp.Record r =>
                let 
                  val pexprlist = Vector.toListMap ( (Record.toVector(r)), 
                      (expression_to_pexpr o (fn (a, b) => b)))  
                  (* we allow only variables and ints in args *)
                  val relemlist = expr_to_relem_list e2
                in
                  (Predicate.Tuplelist pexprlist,relemlist)
                end			        			
              | _ => ((expression_to_pexpr e2),expr_to_relem_list e2))
            val (f'',rf'') = case l of
                SOME pat =>
                let
                  val (sublist,rsublist) = 
                    ((Pattern.bind_pexpr pat pexpr),
                     (Pattern.bind_relem pat relemlist))
                in
                  (print ("\n Apply once : pat is " ^ (CoreML.Pat.visitPat pat) ^ 
                    " while e2 is " ^ (CoreML.visitExp e2) ^"\n");
                    (List.foldr (sublist, f', fn (sub, fr) => F.apply_substitution sub fr),
                    List.foldr (rsublist, rf', fn (sub, rf) => RF.apply_substitution sub rf))
                  )
                end
              | _ => (*case when f is unlabeled*)
                let 
                  fun paramIndex e = 
                    case (Exp.node e) of
                      Exp.Var _ => 0
                      | Exp.App (e1, e2) => 1 + (paramIndex e1)  
                      | _ => (print "\nError function form\n"; assertfalse ())
                  val index = paramIndex func
                  val funname = getFunctionAppName func
                  val vpat = Pat.var (Var.fromString ("local_arg" ^ (Int.toString index)), Type.var(Tyvar.newNoname {equality = false}))
                in
                  (List.foldr ((Pattern.bind_pexpr vpat (expression_to_pexpr e2)), f', fn (sub, fr) => F.apply_substitution sub fr),rf')
                end
            val rel_env = (env,renv,guard)
            (* f2=>f for precondition *)
          in 
            (f'', rf'', 
            [Cs.SubFrame (env, guard, f2, f)], 
            [RCs.SubRFrame (rel_env, rf2,rf)], (*subframing between tuples *)
            e2_cstrs @ subexp_cstrs, 
            e2_rstrs @ subexp_rstrs) 
          end
      | _ => fail "Arrow frames expected in apply_once\n"
  
  (* function application expressions are constrained here *)
  and constrain_application (env, guard, _) (renv,_,rf) 
      func exp polymatching_table = 
    let
      val _ = print ("constrain application ...\n")
      val (func_frame, func_rf, func_cstrs, func_rstrs) = 
        constrainExp func env renv guard polymatching_table
    in 
      apply_once env renv guard exp func_frame 
                func_rf func_cstrs func_rstrs 
                 polymatching_table 
                 func
    end
  
  and constrain_let (env, guard, f) (renv,_,rf) decs body 
                    polymatching_table =
      let 
        val (env',renv',cstrs1,rstrs1,_) = 
          constrain_structure env renv guard decs polymatching_table 
        val (body_frame, body_rframe, cstrs2, rstrs2) =
          constrainExp body env' renv' guard polymatching_table
        val rel_env = (env,renv,guard)
        val rel_env' = (env',renv',guard)
    in
      case (Exp.node body) of (* we don't need this special case in sml. *)
        Exp.Let (_, _) => 
          (body_frame, 
          body_rframe, 
          [Cs.WFFrame (env, body_frame)],
          [RCs.WFRFrame (rel_env, body_rframe)],
          cstrs1 @ cstrs2,
          rstrs1 @ rstrs2)
      | _ =>
        let 
          val f = F.label_like f body_frame
          val rf = RF.label_like rf body_rframe
        in
          (f, rf,
          [Cs.WFFrame (env, f), Cs.SubFrame (env', guard, body_frame, f)], 
          [RCs.WFRFrame (rel_env, rf), RCs.SubRFrame (rel_env', body_rframe, rf)], 
          cstrs1 @ cstrs2,
          rstrs1 @ rstrs2)
        end
    end
  
  (*and constrain_array (env, guard, f) elements =
    let val fs = case f of
      F.Farrow(_, _, f') => (case f' of 
        F.Fconstr(p, l, _) => l
          | _ => assertfalse ())
        | _ => assertfalse()		    	
        fun list_rec (e, (fs, c)) = (fn (f, cs) => (f::fs, cs @ c)) (constrain e env guard)
        val (fs', sub_cs) = List.fold (elements, ([], []), list_rec) 
        fun mksub b a = Cs.SubFrame(env, guard, a, b) 
      in
        (f, Cs.WFFrame(env, f) :: List.map (mksub (List.first fs)) fs', sub_cs)
      end
  *)
  

  and constrain_sequence (env, guard, f) (renv,_,rf) es 
                          polymatching_table =
    let
      val (f,rf,cs,rs) = Vector.fold (es, (f, rf, [], []), 
        (fn (a, (_,_, cs2, rs2)) =>
          let 
            val (f', rf', cs1,rs1) = 
              constrainExp a env renv guard polymatching_table
          in
            (f',rf',cs1@cs2,rs1@rs2)
          end
        ))
    in
        (f,rf,[],[],cs,rs)
    end

  and constrain_assertfalse (_, _, f) (_,_,rf)= (f, rf, [], [],[],[])
  

  and constrain_assert (env, guard, _) (renv, _,rf) e 
                        polymatching_table =
    let 
      val (f, rf, cstrs, rstrs) = 
        constrainExp e env renv guard polymatching_table 
      val f = case f of 
        F.Fconstr (a, b, (subs, F.Qconst[(v1,v2,P.Not (P.True))])) => 
          F.Fconstr (a, b, (subs, F.Qconst[(v1,v2,P.Iff ((B.tag (P.PVar v2)), P.Not (P.True)))]))
        | _ => f
      val guardvar = Var.mk_ident "assert_guard"
      val env = Le.add guardvar f env
      val assert_qualifier =
          (Var.mk_ident "assertion",
           Var.mk_ident "null",
           P.equals (B.tag (P.PVar guardvar)) (P.int_true))
      in 
        (B.mk_unit (), rf, [Cs.SubFrame (env, guard, B.mk_int [], B.mk_int [assert_qualifier])], [],cstrs,[]) 
      end
  
  fun simplylc c = case c of
      Cs.lc c' => c'
                              
  structure QualifierSet = ListSetFn (open Qualifier)
  


  (* Make copies of all the qualifiers where the free identifiers are replaced
     by the appropriate bound identifiers from the environment. *)
  fun instantiate_in_environments cs qs =
    (* Collect all keys (i.e. variable name?) in the env in all cs'(constraints) *)
    let val domains = List.map (cs, (fn c => case #lc_cstr (simplylc c) of 
                          Cs.SubFrame (e,_,_,_) => Lightenv.domain e | Cs.WFFrame (e,_) => Lightenv.domain e))
      
      fun instantiate_qual (q, qualset) =
        let fun instantiate_in_env (d, qset) =
            let val varmap = Common.map_partial (fn path => SOME (Var.toString path, path)) d
                (* Added by He Zhu: This function replaces all instances of named variables 
                 * in a qualifier with the unique paths of the same name in the given environment.
                 *)
            val inv = Qualifier.instantiate varmap q 
            in
              case inv of
                    SOME inv => QualifierSet.add (qset, inv)
                  | NONE => qset
            end
          in List.fold (domains, qualset, instantiate_in_env) end
      in QualifierSet.listItems (List.fold (qs, QualifierSet.empty, instantiate_qual)) end
  


  fun make_frame_error s cstr =
    let fun error_rec cstr' =
        case #lc_orig cstr' of
            Cs.Loc exp =>
              (case #lc_cstr cstr' of
                  Cs.SubFrame (_, _, f1, f2) =>
                    (exp, NotSubtype (F.apply_solution s f1,  F.apply_solution s f2))
                | Cs.WFFrame (_,f) => (exp, IllFormed (F.apply_solution s f)))
          | Cs.Assert exp => (SOME exp, AssertMayFail)
          | Cs.Cstr cstr => error_rec (simplylc cstr)
      in error_rec (simplylc cstr) end
  


  fun report_error outfile frerr = 
    ((case frerr of
          AssertMayFail => TextIO.output(outfile, "@[Assertion may fail@]")
        | NotSubtype (f1, f2) => TextIO.output(outfile, "@[@[" ^ (F.pprint f1) ^ "@]@;<1 2>is not a subtype of@;<1 2>@[" ^ (F.pprint f2) ^ "@]")
        | IllFormed f => TextIO.output(outfile, ("@[Type " ^ (F.pprint f) ^ " is ill-formed")));
      TextIO.flushOut (outfile))
  
  fun report_errors outfile err_li =
      case err_li of
          (e, frerr) :: errs => 
          (case e of 
              SOME e1 => (TextIO.output(outfile, CoreML.visitExp e1); report_error outfile frerr; report_errors outfile errs)
            | NONE => (report_error outfile frerr; report_errors outfile errs);
          TextIO.flushOut (outfile))
        | [] => ()
  
  (* fun lbl_dummy_cstr c = lc { lc_cstr = c, lc_orig = Loc NONE, lc_id = fresh_fc_id () } *)
end
