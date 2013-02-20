structure RelConstraintgen (*: CONSTRAINTGEN *) = 
struct
  open Atoms
  open CoreML
  open HashTable
  open Type_desc
  open Common
  (*open RelFrame*)
  (*open RelConstraint*)
  structure P = Predicate
  structure RP = RelPredicate
  structure C = Common
  structure Cf = Control
  structure Cs = Constraint
  structure B = Builtin
  structure RB = RelBuiltin
  structure Le = Lightenv
  structure RLe = RelLightenv
  structure F = Frame
  structure RF = RelFrame

  datatype error =
      NotSubtype of F.t * F.t
    | IllFormed of F.t
    | AssertMayFail
  
  exception Error of (Exp.t option) * error
  exception Errors of (Exp.t option * error) list
  
  val hash_fn = HashString.hashString
  
  
  fun pprint_debug ( fname :string )
               (ret_cs : Cs.frame_constraint list)
               (env : Le.t)
               (guard : Cs.guard_t)
               (belong_pat : Pat.t)
               (call_deps : ((Pat.t * Pat.t) list) ref)
               (paths : ((Pat.t*P.pexpr*P.t*bool) list) ref)
               (polymatching_table (*: (Var.t, Var.t) HashTable.t*)) =
  let
    val _ = print ( "\n\n-----------  DATA RETURNED BY "^fname^" ---------\n")
    val _ = print "--- 1. Constraints --\n"
    val _ = List.fold (ret_cs,(),
              (fn(c,_) => (
                print (Constraint.pprint c);
                print "\n"
              ))
            )
    val _ = print "-- 2. LightEnv --\n"
    val _ = print (Le.pprint_fenv_except (env,B.is_builtin))
    val _ = print "-- 3. Guards --\n"
    val _ = List.fold (guard,(),
              (fn ((var,i,b),_) => (
                  print ((Var.toString var)^" : "^(Int.toString i)^" : "^(Bool.toString b)^"\n")
              ))
            )
    val _ = print "-- 4. BelongPat --\n"
    val _ = print ((Pat.visitPat belong_pat)^"\n")
    val _ = print "-- 5. Call Dependencis --\n"
    val _ = List.fold (!call_deps,(),
               (fn ((p1,p2),_) => (
                 print ((Pat.visitPat p1)^" --> "^(Pat.visitPat p2)^"\n")
               ))
            )
    val _ = print "-- 6. Path Encoding --\n"
    val _ = List.fold (!paths,(),
              (fn ((pat,pe,pred,bval),_) => (
                print ("["^(Pat.visitPat pat)^"], ["^(P.pprint_pexpr pe)^
                  "], ["^(P.pprint pred)^"], ["^(Bool.toString bval)^"]\n"
                )
              ))
            )
    val _ = print "-- 7. PolyMatching Table --\n"
    val _ = HashTable.foldi
              (fn ((frv1:Var.t),(frv2:Var.t),_) => (
                print ((Var.toString frv1)^" --> "^(Var.toString frv2)^"\n")
              ))
              ()
              polymatching_table
    val _ = print "\n\n\n"
  in
    ()
  end


  fun getFunctionAppName e = 
    case (Exp.node e) of 
      Exp.App (e1, e2) => getFunctionAppName e1
      | Exp.Var (var, _) => (Var.toString (var()))
      | _ => (print ("\nError expression considered as Var " ^ (CoreML.visitExp e) ^ "\n"); assertfalse ())
      
  fun getFunctionApp e = 
    case (Exp.node e) of 
      Exp.App (e1, e2) => getFunctionApp e1
      | Exp.Var (var, _) => (var(), Exp.ty e)
      | _ => assertfalse ()
    
  fun getFunctioinAppPat e = 
    let val (var, ty) = getFunctionApp e
    in
      (Var.toString var, Pat.var (var, ty))
    end
    
  fun getFunctionAppParam e paralist = 
    case (Exp.node e) of 
      Exp.App (e1, e2) =>  
        ((case (Exp.node e2) of
          Exp.Var (var, _) => List.push (paralist, var())
          | Exp.Record r => 
            let fun getFunctionAppRecordParam r =  
                let val record_params = Vector.toListRev (Vector.map (Record.toVector(r), fn (a, b) => b))
                in
                  List.foreach (record_params, fn rp => 
                    case (Exp.node rp) of
                      Exp.Var (var, _) => List.push (paralist, var())
                      | Exp.Record r' => getFunctionAppRecordParam r'
                      | _ => assertfalse ()
                  )
                end
            in
              getFunctionAppRecordParam r
            end
          
          | Exp.Const _ => List.push (paralist, Var.fromString "constvalue")
          | _ => assertfalse ()
        ); getFunctionAppParam e1 paralist)
      | Exp.Var (var, _) => ()
      | _ => assertfalse () 

  val sumdatatypeTable : (Tycon.t, (Con.t * Type_desc.type_desc list) list) hash_table = 
    mkTable ((HashString.hashString) o (Tycon.toString), Tycon.equals) (37, Common.Not_found)
  
  val datatypeTable : (Con.t, (Type_desc.type_desc * bool) list) hash_table = 
    mkTable ((HashString.hashString) o (Con.toString), Con.equals) (37, Common.Not_found)


  fun type_desc exp = Type.toMyType (Exp.ty exp)

  val defaultCons = Con.newString "any"

  fun expression_to_rexpr e =
    let 
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
            | _ => NONE))
    in
      case (Exp.node e) of
          Exp.Const f => (case (constexp_to_int e) of
              SOME i => RP.make_rset [RP.RInt i]
            | NONE => RP.make_null_rset()
          )
        | Exp.Var (varf, _) => RP.make_rrel(defaultCons,RP.make_typedvar(varf()))
        | Exp.App (e1, e2) => (case ((type_desc e),(Exp.node e1)) of
              (Tconstr (tycon,tdlist), Exp.Con (c,_)) =>
                (let
                  val (flags:(bool list)) = List.map ((HashTable.lookup datatypeTable c), (fn(x,y)=>y)) 
                  fun filter_exp e = (case (Exp.node e) of
                      Exp.Var (v,_) =>e2
                    | Exp.Const f => e2
                    | _ => (print ("Apply cons only on vars and consts\n");assertfalse()))
                  val (conargs: (Exp.t list)) = (case (Exp.node e2) of
                      Exp.Record r => 
                      let
                        val exp_list = Vector.toListMap (Record.toVector r,snd)
                      in
                        List.map (exp_list, filter_exp)
                      end
                    | _ => [filter_exp e2])
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
                        | NONE => (print ("only ints allowed in constructor args\n");assertfalse())
                      )
                    | _ => assertfalse()

                  )
                  val (l1,l2) = List.fold2(conargs,flags,([],[]),separate)
                  val set = RP.make_runion ((RP.make_rset l1)::l2)
                in
                  set
                end)
            | _ => RP.make_null_rset()
          )
        | _ =>  RP.make_null_rset()
    end
  
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
      | Exp.Record r => (
        if (Vector.length (Record.toVector r) = 0) then Predicate.PVar (Var.fromString "dummy")
        else Predicate.PVar (Var.mk_ident "dummy")
      ) 
      | _ => Predicate.PVar (Var.mk_ident "dummy")
  
  fun matchcase_exp_to_pexpr e = (* returns pexpr list *)
    case (Exp.node e) of
        (Exp.Record r) => Vector.toListMap ((Record.range r), fn p => expression_to_pexpr p) 
      | (Exp.Var (varf, _)) => [expression_to_pexpr e]
      | _ => (print ("\nUnspported expression when matchcase " ^ (CoreML.visitExp e) ^ "\n"); assertfalse ())
  
  (* Remember generated frames *)		                           
  val flogs : (string, Frame.t) hash_table = HashTable.mkTable (HashString.hashString, (op =)) (101, Not_found)                             
                                  
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
    
		fun cacheDataType v = (* set of mutually recursive datatype definitions *)
			Vector.foreach (v, 
            (fn {cons, tycon, tyvars} => 
                let
                  val mydatatype = Tconstr (tycon, Vector.toListMap (tyvars,fn(v)=>(Tvar v)))
                in
                  ( print "\nassert cacheDataType\n"; 
                    print ("Tycon is " ^ (Tycon.toString tycon) ^ "\n");
                    Vector.foreach (cons, fn {arg, con} => (
                      print ("Constructor is " ^ (Con.toString con) ^ "\n");
                      print ("Arg is " ^ (case arg of SOME arg => CoreML.visitType arg | NONE => "NONE") ^ "\n")
                    ));
                    
                    Vector.foreach (cons, (fn {arg, con} => 
                        let 
                          val tef_list = case arg of 
                            NONE => []
                          | SOME t => 
                            let 
                              val nt = Type.toMyType t 
                            in
                              case (nt) of
                                  Ttuple li => 
                                    List.map (li, fn (Tfield (_, t')) => (t',Type_desc.sametype(t',mydatatype))
                                                  | _ => (print "\nUnknow Type\n"; assertfalse ()))
                                | _ => [(nt,Type_desc.sametype(nt,mydatatype))]
                            end
                          val te_list = List.map (tef_list, fn(x,y)=>x)
                        in
                          HashTable.insert datatypeTable (con, (tef_list));
                          if (HashTable.inDomain sumdatatypeTable tycon) then
                            let val existings = HashTable.lookup sumdatatypeTable tycon
                            in HashTable.insert sumdatatypeTable (tycon, (con, te_list) :: existings) end
                          else
                            HashTable.insert sumdatatypeTable (tycon, [(con, te_list)])
                        end
                         ))
                              
                  )
                end
                ))

      fun getConIndex con ty = 
        let val tyc = Type.deConOpt ty
        in
          case tyc of
            SOME (tyc, _) => 
              if (HashTable.inDomain sumdatatypeTable tyc) then
                let val con_te_list = HashTable.lookup sumdatatypeTable tyc
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
  fun is_not_relation exp ty = case (Exp.node exp, type_desc ty) of
      (_,Tconstr(tycon,tyargs)) => not (HashTable.inDomain sumdatatypeTable tycon)
      (Exp.App(Exp.Var (var,_)),e2) => (String.compare (Var.toString (var ()), "assertfalse") = EQUAL)
    | _ => false
  
  (* Creates a new frame for given expression of given type. *)
  (* desc is Exp.t. ty is Type_desc.t. *)
  fun expr_fresh desc ty = 
    if is_poly_instantiation desc then 
      (* unconstrained frame has Bottom refinement. *)
      Frame.fresh_unconstrained ty sumdatatypeTable 
    else 
      Frame.fresh ty sumdatatypeTable 

  fun rexpr_fresh desc ty = 
    if is_not_relation desc ty then 
      RF.fresh_unconstrained ty sumdatatypeTable 
    else 
      RF.fresh ty sumdatatypeTable 
          
  (* lm as Lam {arg, argType, body = Exp {ty = bodyType, ...}, ...} *)
  (*
   *@param cstrs is the labeled_constraint
   *@param binding_table is the (pat, exp) binding definition table
   *@param call_deps is the (pat, pat) call dependencies list
   *@param binding_frame is the (pat, frame) binding frame definition table
   *@param paths is the path encoding of the program
   *@return a tuple of (fenv, cstrs, binding_table, call_deps, binding_frame)
   *)
  fun constrain_structure initfenv initrenv guard pdecs polymatching_table =
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
            in
              (fpat, (Exp.lambda lm))
            end
        in
          case pdecs of 
            [] => (fenv, renv, cstrs, rstrs) 
          | (Dec.Datatype v) :: pdecs' => 
                let val _ = cacheDataType v in
                  constrain_rec fenv renv guard cstrs rstrs pdecs'
                end
          | (Dec.Exception ca) :: pdecs' => constrain_rec fenv renv guard cstrs rstrs pdecs' 
          | (Dec.Fun {decs, tyvars, ...}) :: pdecs' => 
              let
                val	bindings = Vector.toListMap (decs, binder)
                val (fenv, renv, cstrs', rstrs') 
                    = constrain_bindings fenv renv guard true bindings polymatching_table
              in
                constrain_rec fenv renv guard (cstrs @ cstrs') (rstrs @ rstrs') pdecs'
              end
          | (Dec.Val {rvbs, tyvars, vbs, ...}) :: pdecs' =>
              let
                val	rec_bindings = Vector.toListMap (rvbs, binder)
                val (fenv, renv, cstrs1', rstrs1') = constrain_bindings fenv renv guard true rec_bindings polymatching_table
                val bindings = (Vector.toListMap (vbs, (fn {exp=exp', pat=pat', ...} => ( (pat', exp')))))
                val (fenv, renv, cstrs2', rstrs2') = constrain_bindings fenv renv guard false bindings polymatching_table
              in 
                constrain_rec fenv renv guard (cstrs @ cstrs1' @ cstrs2') (rstrs @ rstrs1' @ rstrs2') pdecs' 
              end
        end
      (*end of constrain_rec*)
    in 
      constrain_rec initfenv initrenv guard [] [] pdecs 
    end
      
  and constrain_and_bind_stub g p pat = (Le.empty 0, RLe.empty 0, [], [])

  and constrain_subexprs_stub u_e g e pats p_t = ([],[],[],[])

  and constrain_bindings env renv guard recflag bindings polymatching_table =
    case recflag of (* return Le.t*(Constraint.labeled_constraint list) *)
      false => List.fold (
                  bindings, (* Pat.t*Exp.t list *)
                  (env, renv,[] ,[]), 
                  (constrain_and_bind guard polymatching_table)
               )
    | true => (*(env,renv,[],[])*)
      let 
        val exprs = List.map (bindings, (fn (a, b) => b))
        val pats = List.map (bindings, (fn (a, b) => a))
        val bindings = List.map (bindings, (fn (p, e) => (p, e, expression_to_pexpr e)))
        val unlabeled_frames = List.map (exprs, (fn e => RF.fresh (Type.toMyType (Exp.ty e)) sumdatatypeTable))
        val unlabeled_env = bind_all bindings unlabeled_frames env
        val (label_frames,_,label_rframes,_) = constrain_subexprs_stub unlabeled_env 
                                                   guard 
                                                   exprs 
                                                   pats 
                                                   polymatching_table
          
        val binding_frames = List.map2 (unlabeled_frames, label_frames, (fn (a, b) => RF.label_like a b))		            
        (* Redo constraints now that we know what the right labels are *)
        val bound_env = bind_all bindings binding_frames env
        val (found_frames, subexp_cstrs) = constrain_subexprs bound_env guard exprs 
            belong_pat pats	binding_table call_deps binding_frame paths	insidefunbindings freevars totalvars polymatching_table	
        fun make_cstr fc pat = lc {lc_cstr = fc, lc_orig = Loc NONE, lc_id = fresh_fc_id (), lc_binding = pat}
        fun build_found_frame_cstr_list (found_frame, binding_f, pat, cs) =
            make_cstr (RWFFrame (bound_env, binding_f)) pat ::
            make_cstr (RSubFrame (bound_env, guard, found_frame, binding_f)) pat :: cs
        val ret_cs = (List.fold3 (found_frames, binding_frames, pats, [], build_found_frame_cstr_list)) @ subexp_cstrs

      in 
        (bound_env, (List.fold3 (found_frames, binding_frames, pats, [], build_found_frame_cstr_list)) @ subexp_cstrs) 
      end
  
  
  (*
   * If pexpr is a function call, and pat is a tuple/record, we name a distinct variable for this pat. And bing it in the env.
   *)
  and tbind env pat frame pexpr =
    let val env = case (Pat.node pat, frame, pexpr) of
            (Pat.Tuple _, Frame.Frecord _, Predicate.PVar record_var) => Le.env_bind_record env pat frame record_var
            | _ => Le.env_bind env pat frame
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
    val renv = RF.env_bind renv (Pat.node pat) rframe
  in
    if (Pattern.is_deep pat) then
      RLe.add (Var.mk_ident "pattern")
        (RB.mk_poly [(Var.mk_ident "pat", Var.mk_ident "pat", RelPattern.desugar_bind pat pexpr)])
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
      val env = Le.env_bind env pat frame
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
      val pexpre = expression_to_pexpr e
      val (env,renv) = tbind env renv pat f rf pexpr rexpr
    in 
      (env, renv, cstrs @ cstrs', rstrs @ rstrs')
      (*(env,renv,cstrs,rstrs)*)
    end
  
  and bind_all bindings fs env = List.foldr2 (bindings, fs, env, (fn ((p, e, px), f, env) => tbind env p f px))
  
  and constrain_subexprs env 
                         guard 
                         es 
                         belong_pat 
                         pats 
                         binding_table 
                         call_deps 
                         binding_frame 
                         paths 
                         insidefunbindings 
                         freevars 
                         totalvars 
                         polymatching_table = 
    if ((List.length pats) = 0) then
      List.foldr (es, ([], []), (fn (e, (fs, cs)) 
        => let val (f, cs') = constrainExp e 
                                          env 
                                          guard 
                                          belong_pat 
                                          binding_table 
                                          call_deps 
                                          binding_frame 
                                          paths 
                                          insidefunbindings
                                          freevars 
                                          totalvars 
                                          polymatching_table 
            in (f :: fs, cs' @ cs) end))
    else 
      List.foldr2 (pats, es, ([], []), (fn (pat, e, (fs, cs)) 
        => let val patty = Pat.ty pat
               val (f, cs') = if (Type.isArrow patty) then 
                        constrainExp e (Lightenv.copy env) guard pat binding_table call_deps binding_frame paths insidefunbindings
                          freevars totalvars polymatching_table (* function : new belong_pat *) 
                        else
                    (print "recursive expr cannot have any type besides function type"; 
                     assertfalse ()) (* non function : depend on toplevel flag *)
          in
             HashTable.insert binding_table (pat, e);
             HashTable.insert binding_frame (pat, f);
             (*print ("\n&&&&" ^ (Frame.pprint f) ^ "\n");*)
             (f :: fs, cs' @ cs)
          end   		
          ))
  and constrain_nullary_constructed expty f = case f of
      RFconstr(tycon,tyargfs,_) => 
      let
        val rexp = RP.make_null_rset ()
        val qual = RB.equality_qualifier defaultCons rexp
        val refn = RF.RQconst [qual]
      in
        RFconstr(tycon,tyargfs,refn)
      end

  and constrainExp e env renv guard polymatching_table = 
  let 
    val _ = print ("Constraining Exp " ^ (CoreML.visitExp e) ^ "\n")
    val desc= (Exp.node e)
    val tyy = type_desc e
    (* lo and behold, for a new frame is born! *)
    val environment = (env, guard, expr_fresh desc tyy)
    val renvironment = (renv, guard, rexpr_fresh desc tyy
    val (f, rf, cstrs, rstrs, rec_cstrs, rec_rstrs) = case desc of
        (   Exp.Const f) =>
            let 
              val(f,cstrs,rec_cstrs) =  constrain_constant (f())
              val rf = RF.fresh_unconstrained tyy sumdatatypeTable 
            in
              (f,rf,cstrs,[],rec_cstrs,[])
            end
          | Exp.Con (c, targs) => (* case of unary constructors being rhs of binding *)
              let
                val (f,cstrs,rec_cstrs) = (case (Con.toString c) of
                    "true" => (F.Fconstr (Tycon.bool, [], Frame.fresh_true ()), [], [])
                  | "false" => (F.Fconstr (Tycon.bool, [], Frame.false_refinement), [], []) 
                  |_  => (print ("\nconstructor frame generating error"); assertfalse ()))(* "nil", "ref" is not currently supported *)
                val rpred = RP.requals ()
                val rf = constrain_nullary_constructed tyy (#3 renvironment)
              in
                (f, rf, cstrs,[], rec_cstrs, [])
              end
          | Exp.Record r => constrain_record environment renvironment (Record.toVector(r)) polymatching_table
          | Exp.Case {rules, test, ...} => 
            let
              val rlist = Vector.toListMap (rules, (fn {exp, pat, ...} => (pat, exp)))
            in
              constrain_match environment renvironment test rlist polymatching_table
            end 
          | Exp.Var (var, targs) => constrain_identifier environment renvironment (var()) e polymatching_table   

          (* All primary operators like <,>,<= etc are also Exp.App *)
          (*| Exp.App (e1, e2) => (case (Exp.node e1) of 
              (Exp.Con (c, targs)) => 
              let
                val e2list = case (Exp.node e2) of Exp.Record e2 => (Vector.toListMap ((Record.toVector e2), (fn (a, b) => b)))
                                | _ => [e2]
                val tycon1 = case tyy of Type_desc.Tconstr (tyc, _) => tyc | _ => (print "\nIll constructor\n"; assertfalse ()) 
                val tylist = List.map (HashTable.lookup datatypeTable c handle Not_found => [],
                    (fn(x,y)=>x)) (* built-in constructor *)
                val t = Tconstr (tycon1, tylist)
                val sumf = #3 environment
                val f = case sumf of
                  F.Fsum (_, fs, _) => 
                    let val f = List.peek (fs, fn (c', f) => Con.equals (c, c'))
                      val f =  case f of SOME (_,f) => f | NONE => (print "\nIll type from a datatype\n"; assertfalse ())
                    in Frame.unfoldRecursiveFrame f tycon1 fs end
                  | F.Fconstr (tcc, fls, r) => 
                    if (String.equals ("::", Con.toString c)) then F.Fconstr (tcc, (List.first fls :: fls), r) (* This is considered as unsafe *)
                    else sumf
                  | _ => (print "\nIll sum type from a datatype\n"; assertfalse ())	      								
              in
                constrain_constructed (env, guard, f) 
                                      t 
                                      e2list 
                                      belong_pat 
                                      binding_table 
                                      call_deps 
                                      binding_frame 
                                      paths 
                                      insidefunbindings 
                                      freevars 
                                      totalvars 
                                      polymatching_table
              end
            | (Exp.Var (var, targs)) => if (String.compare (Var.toString (var ()), "assert") = EQUAL) then
                            constrain_assert environment e2 belong_pat binding_table call_deps binding_frame paths insidefunbindings
                              freevars totalvars polymatching_table
                          else if (String.compare (Var.toString (var ()), "assertfalse") = EQUAL) then
                            constrain_assertfalse environment
                          (*else if (String.compare (Var.toString (var ()), "fromList_0") = EQUAL)
                              then case (Exp.node e2) of elements => constrain_array environment elements
                                             | _ => assertfalse ()
                              else*) 
                          else if (String.compare (Var.toString (var ()), "&&") = EQUAL orelse 
                               String.compare (Var.toString (var ()), "||") = EQUAL ) then
                            case (Exp.node e2) of
                              Exp.Record e2 =>
                                let val funname = Var.toString (var ())
                                  val lr = Vector.toListMap ((Record.toVector e2), (fn (a, b) => b))
                                  val l = List.first lr
                                  val r = List.last lr
                                  val (fl, cstr1) = constrainExp l env guard belong_pat binding_table call_deps
                                        binding_frame paths insidefunbindings freevars totalvars polymatching_table
                                  val (fr, cstr2) = constrainExp r env guard belong_pat binding_table call_deps
                                        binding_frame paths insidefunbindings freevars totalvars polymatching_table
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
                                    (Builtin.and_frame pl pr, [], cstr1 @ cstr2)
                                  else
                                    (Builtin.or_frame pl pr, [], cstr1 @ cstr2)
                                end
                              | _ => (print "\nassertion && || syntax ill-formed\n"; assertfalse ())	
                          else if (String.compare (Var.toString (var ()), "not") = EQUAL) then
                            let val (f, cstr) = constrainExp e2 env guard belong_pat binding_table call_deps
                                        binding_frame paths insidefunbindings freevars totalvars polymatching_table
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
                              (Builtin.not_frame p, [], cstr)
                            end
                          else constrain_application environment 
                                                     e1 
                                                     e2 
                                                     belong_pat 
                                                     binding_table 
                                                     call_deps 
                                                     binding_frame 
                                                     paths 
                                                     insidefunbindings 
                                                     freevars 
                                                     totalvars 
                                                     polymatching_table
            | _ => constrain_application environment e1 e2 belong_pat binding_table call_deps binding_frame paths insidefunbindings
                freevars totalvars polymatching_table)
        | Exp.Let (ds, e) => constrain_let environment 
                                          (Vector.toList ds) 
                                          e 
                                          belong_pat 
                                          binding_table 
                                          call_deps 
                                          binding_frame 
                                          paths 
                                          insidefunbindings
                                          freevars 
                                          totalvars 
                                          polymatching_table
        | Exp.List es => constrain_list environment 
                                        es 
                                        belong_pat 
                                        binding_table 
                                        call_deps 
                                        binding_frame 
                                        paths 
                                        insidefunbindings 
                                        freevars 
                                        totalvars 
                                        polymatching_table
        | Exp.Seq es => constrain_sequence environment es belong_pat binding_table call_deps binding_frame paths insidefunbindings
                    freevars totalvars polymatching_table
        | Exp.Lambda l => constrain_lambda environment 
                                            l 
                                            belong_pat 
                                            binding_table 
                                            call_deps 
                                            binding_frame 
                                            paths 
                                            insidefunbindings
                                            freevars 
                                            totalvars 
                                            polymatching_table
        *)
        | Exp.EnterLeave (e, si) => (print "We do not check EnterLeave"; assertfalse ())
        | Exp.Handle {catch, handler, try} => (print "We don not check Handle"; assertfalse ())
        | Exp.PrimApp {args, prim, targs} => (print "We do not check PrimApp"; assertfalse ())
        | Exp.Raise e => (print "We do not check Raise"; assertfalse ())
        | _ => (assertfalse())
      in 
        log_frame e f; (f, (List.map (cstrs, (label_constraint e belong_pat))) @ rec_cstrs)
      end
  
  (* rframes for constants are normal frames *)
  and constrain_constant cons =
    let
      val cs = (case cons of 
           Const.IntInf n => 
            ((B.mk_int [B.equality_qualifier (P.PInt (IntInf.toInt n))], [], []))
         | Const.Null => (B.uUnit, [], [])
         | Const.Real _ => (B.uFloat, [], [])
         | Const.Word n => 
            (B.mk_int [B.equality_qualifier (P.PInt (IntInf.toInt (WordX.toIntInfX n)))], [], [])
         | Const.WordVector _ => assertfalse ()
       )
    in
      cs
    end
  
  (* 
   * By constructor here, we temporarily do not consider constructor for list or array.
   * Parameter cstrdesc is the type of the constructor
   * Parameter args is the parameters of this constructor
   *)
  and constrain_constructed (env, guard, f) 
                            cstrdesc 
                            args 
                            belong_pat 
                            binding_table 
                            call_deps 
                            binding_frame 
                            paths 
                            insidefunbindings 
                            freevars 
                            totalvars 
                            polymatching_table =
    case f of
      F.Fconstr (path, tyargframes, refn) =>
        let (* Seeking the formal types of arguments *)
          val cstrargs = (*F.fresh_constructor cstrdesc f *)
            case f of F.Fconstr (_, fl, _) => fl | _ => (print ("\nConstructor with ill type " ^ (Frame.pprint f) ^ "\n"); assertfalse ())
          (* Seeking the actual types of args which are actuals *)
          val _ = print "go here0\n"
          val (argframes, argcstrs) = constrain_subexprs env guard args belong_pat [] (* not pats for them *) 
                          binding_table call_deps binding_frame paths insidefunbindings freevars totalvars polymatching_table
          val _ = print "go here\n"
          val ret_cs = Cs.WFFrame(env, f) :: ((List.map2 (argframes, cstrargs, (fn (arg, formal) => Cs.SubFrame(env, guard, arg, formal)))) @ (lcstrs_to_fcstrs argcstrs))
          val _ = pprint_debug "constrain_constructed"
                               ret_cs
                               env
                               guard 
                               belong_pat 
                               call_deps 
                               paths 
                               polymatching_table

        in
            (f,
             Cs.WFFrame(env, f) :: (List.map2 (argframes, cstrargs, (fn (arg, formal) => Cs.SubFrame(env, guard, arg, formal)))),
             argcstrs) end
        | _ => assertfalse ()
  
  and is_sum_type ty = case ty of
      Tconstr(tycon,tyargs) => HashTable.inDomain sumdatatypeTable tycon
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
          (RCs.RSubFrame (rel_env,rfsub,rfsup)) :: rcs_rest
        val (ret_f, cur_cs) = case f of
            F.Frecord (recframes, _) => 
              let 
                fun field_qualifier ((_, name), fexpr) = B.field_eq_qualifier name (expression_to_pexpr fexpr) 
                (* In case of tuples, names are "1", "2".. So, qualifier would
                   be x11.1 = pfexp1, x11.2 = pfexp2...*)
                val ret_f = F.Frecord (recframes, ([], F.Qconst (List.map2 (recframes, sorted_exprs, field_qualifier))))
                val (cur_cs : Cs.frame_constraint list) = Cs.WFFrame (env, f) :: List.fold2 (subframes, recframes, [], subframe_field)
                val (slist : Cs.frame_constraint list) = lcstrs_to_fcstrs subexp_cs
                val ret_cs = cur_cs@slist
              in
                (ret_f, cur_cs)
              end
            | _ => assertfalse ()
        val (ret_rf, cur_rcs) = case rf of
            RF.RFrecord (recrframes, _) => 
              let 
                fun field_rqualifier_list ((_, name), fexpr) acc = 
                let
                  val ftype = type_desc fexpr
                in
                  if (is_sum_type ftype) then 
                    (RB.field_eq_qualifier name defaultCons (expression_to_rexpr fexpr))::acc
                  else
                    acc
                end
                val ref_rquals = List.fold2(recframes,sorted_exprs,[],field_rqualifier_list)
                val refn = if(List.length ref_rquals > 0) 
                  then ([],RF.RQconst ref_rquals) 
                  else RF.fresh_refinementvar RF.RBottom
                val ret_rf = RF.RFrecord (recrframes,refn)
                val rel_env = (env,renv,guard)
                val (cur_rcs : RCs.rframe_constraint list) = 
                  RCs.WFRFrame (rel_env, rf) :: List.fold2 (subrframes, recrframes, [], subrframe_field rel_env)
              in
                (ret_rf, cur_rcs)
              end
            | _ => assertfalse ()
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
      val env = matchcase_tbind env pat matchf match_pexpr
      val renv = bind_rexpr renv pat matchrf match_rexpr
      (* Now, env contains mapping bewteen  
         1. pat frame and matchf
         2. forevery pat' inside pat and
              for corresponding pexpr' inside matche
                pat' -> pexpr'
       *)
      val (fe, subcs) = constrainExp e env renv guard polymatching_table
      (* generated constraints refer to extended env and updated guard *)
      val ret_cs = (Cs.SubFrame (env, guard, fe, f))::(lcstrs_to_fcstrs subcs)
    in 
      (Cs.SubFrame (env, guard, fe, f), subcs) 
    end
  
  (* e is the test; pexps are paris of (pat, exp) *)
  and constrain_match (environment as (env, guard, f)) 
                      (renvironment as (renv,guard,rf))
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
                    "true" => grd2
                  | "false" => grd3
                  | _ => (print "bool cons not in true|false\n";assertfalse())
                )
                val (f', rf', cstrs', rstrs') = constrainExp e env' renv grd' polymatching_table
                val rel_env = (env',renv,grd')
                val subflist = Cs.SubFrame(env',grd', f', f) :: fli
                val subrflist = RCs.SubRFframe (rel_env,grd', rf', rf) :: rfli
              in
                (subflist,subrflist,cstrs'@cli,rstrs'@rli)
              end
            | _ =>(print "if-then-else error1\n";assertfalse())))
        val rel_env = (env',renv,guard)
      in
        (f, Cs.WFFrame(env, f) :: subflist, RCs.WFRFrame(rel_env,rf)@subrflist,cstrs1 @ subclist, rstrs1@subrclist)
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
        val test_pexpr = matchcase_exp_to_pexpr e
        val test_rexpr = expression_to_rexpr e (* no spl treatment*)
        val cases = List.mapi (pexps, fn (i, (pat, e')) => 
            (constrain_case environment renvironment matchf match_pexpr match_rexpr polymatching_table 
                                                                            (guardvar, i, (pat, e'))))
        val cstrs = List.map (cases, (fn (a, b, c, d) => a))
        val rstrs = List.map (cases, (fn (a, b, c, d) => b))
        val subcstrs = List.map (cases, (fn (a, b, c, d) => c))
        val subrstrs = List.map (cases, (fn (a, b, c, d) => d))
      in 
        (f, rf, Cs.WFFrame (env, f) :: cstrs, 
        RCs.WFRFrame (env, rf) :: rstrs, 
        List.concat (matchcstrs :: subcstrs),
        List.concat (matchrstrs :: subrstrs)) 
      end
  
  and constrain_lambda (env, guard, f) 
                        lam 
                        belong_pat 
                        binding_table 
                        call_deps 
                        binding_frame 
                        paths 
                        insidefunbindings 
                        freevars 
                        totalvars 
                        polymatching_table = (
    let val (pat, e') = (fn {arg=arg', argType=argType', body=body', mayInline=mayInline'} 
      => ((Pat.var (arg', argType')), body')) (Lambda.dest lam)
      in case f of
          (F.Farrow (_, f, unlabelled_f')) =>
            (* \pat.e --> Gamme;guard;pat:f |- e:?? *)
            let val env' = Le.env_bind env pat f
            val (f'', cstrs) = constrainExp e' 
                                            env' 
                                            guard 
                                            belong_pat 
                                            binding_table 
                                            call_deps 
                                            binding_frame 
                                            paths 
                                            insidefunbindings 
                                            freevars 
                                            totalvars 
                                            polymatching_table
            val f' = F.label_like unlabelled_f' f''
            val f = F.Farrow (SOME pat, f, f')
            val ret_cs = [Cs.WFFrame (env, f), Cs.SubFrame (env', guard, f'', f')] @ (lcstrs_to_fcstrs cstrs)
            val _ = pprint_debug "constrain_lambda"
                                 (ret_cs)
                                 env
                                 guard 
                                 belong_pat 
                                 call_deps 
                                 paths 
                                 polymatching_table
          in
            (f, [Cs.WFFrame (env, f), Cs.SubFrame (env', guard, f'', f')], cstrs)
          end
      | _ => assertfalse ()
    end)

  and instantiate_id id f env e polymatching_table = (
    print ("instantiate_id " ^ (Var.toString id) ^ "...\n");
    let 
      val env_f =
      (Le.find id env) handle Not_found => ((*print "H not found";*)
        (let 
           val tyy = Type.toMyType (Exp.ty e)
         in Frame.fresh_without_vars tyy sumdatatypeTable end))
         (* in this case, we would be instantiating fresh with fresh *)
      val _ = print ("env_f is " ^ (Frame.pprint env_f) ^ "\n")
      val _ = print "instantiating...\n"
      val new_f = F.instantiate env_f f polymatching_table
      val _ = print ("new frame after instantiation is "^(Frame.pprint new_f)^"\n")
    in 
      new_f
    end)
    
    (* responsible for looking up constraints for existing identifiers  and instantiating them *)
    and constrain_identifier (env, guard, f) id e freevars totalvars polymatching_table = (
      (*print "constraint identifier \n";*)
      case (Type.toMyType (Exp.ty e)) of
          Type_desc.Tconstr (tycon1, type_expr1) => (* Based Identifier *)
          (* variables come here as ty is Tycon.defaultInt()  *)
        let 
            val refn =
              if Le.mem id env then 
                B.equality_refinement (expression_to_pexpr e) 
              else F.empty_refinement
            (* id's frame is instantiated with the current frame
               and trivial {=id} refinement is applied *)
            val nf = F.apply_refinement refn (instantiate_id id f env e polymatching_table)
            (* update frame of id in free/total vars table *)
            val _ = if (HashTable.inDomain freevars id) then 
                      (* We should never reach here, as mlton is whole-program *)
                      HashTable.insert freevars (id, nf) 
                    else ()
            val _ = if (HashTable.inDomain totalvars id) then HashTable.insert totalvars (id, nf) else ()
        in (nf, [], [])
        end 
      | Type_desc.Tvar _ => 
        let val refn =
            if Le.mem id env then B.equality_refinement (expression_to_pexpr e) else F.empty_refinement
            val nf = F.apply_refinement refn (instantiate_id id f env e polymatching_table)
            val _ = if (HashTable.inDomain freevars id) then HashTable.insert freevars (id, nf) else ()
            val _ = if (HashTable.inDomain totalvars id) then HashTable.insert totalvars (id, nf) else ()
        in (nf, [], [])
        end 
      | _ => let 
               val _ = print ("before instantiate_id, frame is " ^ (Frame.pprint f))
               val f = instantiate_id id f env e polymatching_table
               val _ = print ("after instantiate_id, frame is " ^ (Frame.pprint f))
               val _ = Lightenv.update id f env
               val _ = if (HashTable.inDomain freevars id) then HashTable.insert freevars (id, f) else ()
               val _ = if (HashTable.inDomain totalvars id) then HashTable.insert totalvars (id, f) else ()
             in 
               (f, [Cs.WFFrame(env, f)], []) 
             end
  )
  
  and apply_once env 
                 guard 
                 (e, (f, cstrs(* =[] *), subexp_cstrs(* when e1 is an expr*))) 
                 belong_pat 
                 binding_table 
                 call_deps 
                 binding_frame 
                 paths 
                 insidefunbindings 
                 freevars 
                 totalvars 
                 polymatching_table 
                 func = 
    case (f, e) of
        (*l: arg_pat, f: arg_frame, f': return_frame*)
        (F.Farrow (l, f, f'), e2) =>
          let 
            (* e2_cstrs contain constrains generated on tuple if e2 is tuple.
               eg: v.1=x_0, v.2 = x_1 ...*)
            val (f2, e2_cstrs) = constrainExp e2 
                                                env 
                                                guard 
                                                belong_pat 
                                                binding_table 
                                                call_deps 
                                                binding_frame 
                                                paths 
                                                insidefunbindings 
                                                freevars 
                                                totalvars 
                                                polymatching_table
            (* f'' is f' after substituting actuals for formals *)
            val f'' = case l of
                SOME pat =>
                  (
                  print ("\n Apply once : pat is " ^ (CoreML.Pat.visitPat pat) ^ " while e2 is " ^ (CoreML.visitExp e2) ^"\n");
                  case (Exp.node e2) of
                    Exp.Record r =>
                      (
                      let 
                        val pexprlist = Vector.toListMap (
                            (Record.toVector(r)), 
                            (expression_to_pexpr o (fn (a, b) => b))
                            (* pexprlist should be [PVar(Var(x)), PVar(Var(y))] *)
                        )  
                        val sublst (* Frame.substitution list *) = 
                          (* will return a list of pexpr1=v.1, pexpr.2=v.2 .. *)
                          (* [
                                (Pat.Var(Var(a),Proj(1,Tuplelist(pexprlist))),
                                (Pat.Var(Var(b),Proj(2,Tuplelist(pexprlist))),
                             ] 
                          *)
                          (Pattern.bind_pexpr pat (Predicate.Tuplelist pexprlist))
                      in
                        (* will now substitute all a,b,c.. in f' with pat.1, pat.2... *)
                        (* F.Fconstr(TyCon.bool,[], (sublist,Qcons[(Var(">="),Var(z),pred)])) 
                           where pred is Iff( (FunApp("__tag",[Pvar(z)])), Atom((Pvar(a),P.Ge,Pvar(b))))
                        *)
                        List.foldr (sublst, f', fn (sub, fr) => F.apply_substitution sub fr)
                      end			        			
                      ) 		        		
                    | _ => List.foldr ((Pattern.bind_pexpr pat (expression_to_pexpr e2)), f', fn (sub, fr) => F.apply_substitution sub fr))
              | _ => (
                let 
                  fun paramIndex e = 
                    case (Exp.node e) of
                      Exp.Var _ => 0
                      | Exp.App (e1, e2) => 1 + (paramIndex e1)  
                      | _ => (print "\nError function form\n"; assertfalse ())
                  val index = paramIndex func
                  val funname = getFunctionAppName func
                  val vpat = Pat.var (Var.fromString ("local_arg" ^ (Int.toString index)), Type.var(Tyvar.newNoname {equality = false}))
                in	(* Problem here: Not considering record *)
                  List.foldr ((Pattern.bind_pexpr vpat (expression_to_pexpr e2)), f', fn (sub, fr) => F.apply_substitution sub fr)
                end
              )
            val _ = print ("After args instantiation, returnable frame is "^(Frame.pprint f')^"\n")
            (* f2=>f for precondition *)
            (* or is it f2=>f''', where f''' is [sublist] f ?*)
            val ret_cs = (Cs.SubFrame (env, guard, f2, f) :: cstrs)@(lcstrs_to_fcstrs (e2_cstrs @ subexp_cstrs))
            val _ = pprint_debug "constrain_application - apply_once"
                                 (ret_cs)
                                 env
                                 guard 
                                 belong_pat 
                                 call_deps 
                                 paths 
                                 polymatching_table
          in 
            (f'', Cs.SubFrame (env, guard, f2, f) :: cstrs, e2_cstrs @ subexp_cstrs) 
          end
      | _ => assertfalse ()
  
  (* function application expressions are constrained here *)
  and constrain_application (env, guard, _) 
                            func 
                            exp 
                            belong_pat 
                            binding_table 
                            call_deps 
                            binding_frame 
                            paths 
                            insidefunbindings 
                            freevars 
                            totalvars 
                            polymatching_table = 
    (let
      val _ = print ("constrain application ...\n" ^ (CoreML.visitExp func) ^ " " ^ (CoreML.visitExp exp))
      val (func_frame, func_cstrs) = constrainExp func 
                                                  env 
                                                  guard 
                                                  belong_pat 
                                                  binding_table 
                                                  call_deps 
                                                  binding_frame 
                                                  paths 
                                                  insidefunbindings
                                                  freevars 
                                                  totalvars 
                                                  polymatching_table
    in 
      print ("\n\n THE BELONG_PAT IS " ^ (Pat.visitPat belong_pat) ^ " \n\n");
      (case (Exp.node func) of
        (Exp.Var (var, targs)) => 
          (* So, fn is added to call deps only if it is named. *)
          ((*print ("pushing " ^ (Pat.visitPat (Pat.var (var(), Exp.ty func)))) ;*) List.push (call_deps, (belong_pat, Pat.var (var(), Exp.ty func))))
        | _ => ());
      apply_once env 
                 guard 
                 (exp, (func_frame, [], func_cstrs)) 
                 belong_pat 
                 binding_table 
                 call_deps 
                 binding_frame 
                 paths 
                 insidefunbindings 
                 freevars 
                 totalvars 
                 polymatching_table 
                 func
    end)
  
  and constrain_let (env, guard, f) 
                    decs 
                    body 
                    belong_pat 
                    binding_table 
                    call_deps 
                    binding_frame 
                    paths 
                    insidefunbindings 
                    freevars 
                    totalvars 
                    polymatching_table =
      let 
        val renv = RLe.empty 0
        val (env',renv',cstrs1,rstrs1) = 
          constrain_structure env renv guard decs polymatching_table 
        (* let bindings only extend the environment. So we pass
           extended env to constrain body. However, constraints generated
           inside above call refer to correct (updated) guard_t *)
        val (binding_frame',call_deps',paths',insidefunbindings',binding_table') = 
            (binding_frame,call_deps,paths,insidefunbindings,binding_table)
        val (body_frame, cstrs2) = constrainExp body 
                                                env' 
                                                guard 
                                                belong_pat 
                                                binding_table 
                                                call_deps 
                                                binding_frame 
                                                paths 
                                                insidefunbindings 
                                                freevars 
                                                totalvars 
                                                polymatching_table
        val _ = (Common.mergeHashTable binding_table binding_table'; 
                List.foreach ((!call_deps'), fn cd => List.push (call_deps, cd)); 
                List.foreach ((!paths'), fn pt => List.push (paths, pt));
                Common.mergeHashTable binding_frame binding_frame';
                Common.mergeHashTable insidefunbindings insidefunbindings')
      (*val _ = print "In constrain_let now \n"
      val _ = (print "Constraints from the lets are : "; List.foreach(cstrs1, fn (lc c) => print ((Constraint.pprint (#lc_cstr c)) ^"\n")))
      val _ = print "In body now \n"
      val _ = (print "Constraints from the body are : "; List.foreach(cstrs2, fn (lc c) => print ((Constraint.pprint  (#lc_cstr c)) ^"\n")))*)
    in
        case (Exp.node body) of
            Exp.Let (_, _) => (body_frame, [Cs.WFFrame (env, body_frame)], cstrs1 @ cstrs2)
          | _ =>
            let (*val _ = print "\nbefore labelling\n"*) 
                val f = F.label_like f body_frame
                (*val _ = print "\nend labelling\n" *)
                val ret_cs = ([Cs.WFFrame (env, f), Cs.SubFrame (env', guard, body_frame, f)])@(lcstrs_to_fcstrs (cstrs1 @ cstrs2))
              val _ = pprint_debug "constrain_let"
                                   (ret_cs)
                                   env
                                   guard 
                                   belong_pat 
                                   call_deps 
                                   paths 
                                   polymatching_table
            in
              (f, [Cs.WFFrame (env, f), Cs.SubFrame (env', guard, body_frame, f)], cstrs1 @ cstrs2)
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
  
  (* Our tool currently only consider list as array *)
  and constrain_list (env, guard, f) 
                     elements 
                     belong_pat 
                     binding_table 
                     call_deps 
                     binding_frame 
                     paths 
                     insidefunbindings 
                     freevars 
                     totalvars 
                     polymatching_table =
    let 
      val (f, fs) = case f of
          F.Fconstr(p, l, _) => (F.Fconstr(Tycon.list, l, B.size_lit_refinement(Vector.length elements)), l)
          | _ => assertfalse () 	
      fun list_rec (e, (fs, c)) = (fn (f, cs) => (f::fs, cs @ c)) (constrainExp e env guard 
          belong_pat binding_table call_deps binding_frame paths insidefunbindings freevars totalvars polymatching_table)
      val (fs', sub_cs) = List.fold ((Vector.toList elements), ([], []), list_rec) 
      fun mksub b a = Cs.SubFrame(env, guard, a, b) 
    in
      (f, Cs.WFFrame(env, f) :: List.map (fs', (mksub (List.first fs))), sub_cs)
    end
  

  and constrain_sequence (env, guard, f) 
                          es 
                          belong_pat 
                          binding_table 
                          call_deps 
                          binding_frame 
                          paths 
                          insidefunbindings 
                          freevars 
                          totalvars 
                          polymatching_table =
    Vector.fold (es, (f, [], []), (fn (a, (_, nulllist, cs2)) =>
                let val (f', cs1) = constrainExp a 
                                                 env 
                                                 guard 
                                                 belong_pat 
                                                 binding_table 
                                                 call_deps 
                                                 binding_frame 
                                                 paths 
                                                 insidefunbindings 
                                                 freevars 
                                                 totalvars 
                                                 polymatching_table
                in
                  (f', nulllist, cs1 @ cs2)
                end
              ))
  

  and constrain_assertfalse (_, _, f) = (f, [], [])
  

  and constrain_assert (env, guard, _) 
                        e 
                        belong_pat 
                        binding_table 
                        call_deps 
                        binding_frame 
                        paths 
                        insidefunbindings 
                        freevars 
                        totalvars 
                        polymatching_table =
    let val (f, cstrs) = constrainExp 
                         e 
                         env 
                         guard 
                         belong_pat 
                         binding_table 
                         call_deps 
                         binding_frame 
                         paths 
                         insidefunbindings 
                         freevars 
                         totalvars 
                         polymatching_table 
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
           
      val _ = case f of 
          F.Fconstr (a, b, (subs,F.Qconst[(v1,v2,P.Iff (v3,p))])) => 
            if Predicate.logic_equals_pexp v3 (B.tag (P.PVar v2)) then 
              List.push (paths, (belong_pat, (B.tag (P.PVar guardvar)), (Predicate.apply_substs subs p), true))
            else (print "Error: assert unknown frame encountered."; assertfalse ())
          | _ => (print "Error: assertion ill formed1 "; print (Frame.pprint f); assertfalse ())
      val ret_cs = [Cs.SubFrame (env, guard, B.mk_int [], B.mk_int [assert_qualifier])] @ (lcstrs_to_fcstrs cstrs)
      val _ = pprint_debug "constrain_assert"
                           (ret_cs)
                           env
                           guard 
                           belong_pat 
                           call_deps 
                           paths 
                           polymatching_table
      in 
        (B.mk_unit (), [Cs.SubFrame (env, guard, B.mk_int [], B.mk_int [assert_qualifier])], cstrs) 
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
  
  (* Inferred frame should be a subtype of the frame given by users or third party tools *)
  fun mfm fenv p f = 
    if Le.mem p fenv
    then
      let val f' = Le.find p fenv 
      in SOME (Cs.SubFrame (fenv, [], f', F.label_like f f')) end
    else NONE 
    
  (*fun display_frame s name fr = "Pat: " ^ (Var.toString name) ^ " Type: " ^ (Constraint.pprint_with_solution fr s)
  
  fun display_result fenv str s = 
    let fun display fenv r str s = 
      case str of 
            [] => r
          | (Dec.Datatype v) :: pdecs' => display fenv r pdecs' s						     
        | (Dec.Exception ca) :: pdecs' => display fenv r pdecs' s
        | (Dec.Fun {decs, tyvars, ...}) :: pdecs' => 
              let val	names = Vector.toListMap (decs, (fn {lambda=lm, var=var'} => var'))
                in
                  let val r' = List.fold (names, r, fn (name, r) => (r ^ (display_frame s name (Lightenv.find name fenv)) ^ "\n"))
                in (display fenv r' pdecs' s) end
                end					        	
            | (Dec.Val {rvbs, tyvars, vbs, ...}) :: pdecs' =>
                let val	names = Vector.toListMap (rvbs, (fn {lambda=lm, var=var'} => var'))
                          @
                          Common.flatten (Vector.toListMap (vbs, (fn {exp=exp', pat=pat', ...} => Pattern.vars pat')))
          in
            let val r' = List.fold (names, r, fn (name, r) => (r ^ (display_frame s name (Lightenv.find name fenv)) ^ "\n"))
                in (display fenv r' pdecs' s) end
              end
      in display fenv "" str s end*)
end
