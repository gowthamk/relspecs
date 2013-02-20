(*signature CONSTRAINTGEN = 
	sig
		include CORE_ML
				
		datatype error =
		    NotSubtype of Frame.t * Frame.t
		  | IllFormed of Frame.t
		  | AssertMayFail
			
		exception Error of (Exp.t option) * error
		exception Errors of (Exp.t option * error) list
		
		val report_error: IOUtil.outstream -> error -> unit
		val report_errors: IOUtil.outstream -> (Exp.t option * error) list -> unit 
				
		val expression_to_pexpr : Exp.t -> Predicate.pexpr
		
		val matchcase_exp_to_pexpr : Exp.t -> Predicate.pexpr list
		val getFunctionAppName : Exp.t -> string
		val getFunctioinAppPat : Exp.t -> (string * CoreML.Pat.t)
		val pat_var : CoreML.Pat.t -> Var.t
		val pat_vars : CoreML.Pat.t => Var.t list
		val pat_eq : Pat.t * Pat.t -> bool
	end
*)	
(* Note: locations where belong_pat is updated is marked with
   new belong_pat *)
structure Constraintgen (*: CONSTRAINTGEN *) = 
	struct
		open Atoms
		open CoreML
		open HashTable
		open Type_desc
		open Common
		open Frame
		open Constraint
		structure P = Predicate
		structure C = Common
		structure Cf = Control
		structure B = Builtin
		structure Le = Lightenv
		structure F = Frame

		datatype error =
		    NotSubtype of F.t * F.t
		  | IllFormed of F.t
		  | AssertMayFail
		
		exception Error of (Exp.t option) * error
		exception Errors of (Exp.t option * error) list
		
		val hash_fn = HashString.hashString
		
    
    fun pprint_debug ( fname :string )
                 (ret_cs : frame_constraint list)
                 (env : Le.t)
                 (guard : guard_t)
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
		     

    fun lcstrs_to_fcstrs (lcstrs : labeled_constraint list) =
      List.map (lcstrs,
        (fn (lc lcstr) => #lc_cstr lcstr)
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
		
		val sumdatatypeTable : (Tycon.t, (Con.t * Type_desc.type_desc list) list) hash_table = 
			mkTable ((HashString.hashString) o (Tycon.toString), Tycon.equals) (37, Common.Not_found)
		
		val datatypeTable : (Con.t, Type_desc.type_desc list) hash_table = 
			mkTable ((HashString.hashString) o (Con.toString), Con.equals) (37, Common.Not_found)
			
		fun cacheDataType v = (* set of mutually recursive datatype definitions *)
			Vector.foreach (v, 
            (fn {cons, tycon, tyvars} => (
            		print "\nassert cacheDataType\n"; 
            		print ("Tycon is " ^ (Tycon.toString tycon) ^ "\n");
            		Vector.foreach (cons, fn {arg, con} => (
            			print ("Constructor is " ^ (Con.toString con) ^ "\n");
            			print ("Arg is " ^ (case arg of SOME arg => CoreML.visitType arg | NONE => "NONE") ^ "\n")
            		));
            		
            		Vector.foreach (cons, (fn {arg, con} => 
            								let val te_list = case arg of 
            									  NONE => []
            									| SOME t => 
            										let val nt = Type.toMyType t 
            										in
	            										case (nt) of
	            											  Ttuple li => List.map (li, fn (Tfield (_, t')) => t' 
	            											  								| _ => (print "\nUnknow Type\n"; assertfalse ()))
	            											| _ => [nt]
            										end
            								in (* store in datatype table the constructor with its corresponding tycon and parameter type list *)
            									HashTable.insert datatypeTable (con, (te_list));
            									if (HashTable.inDomain sumdatatypeTable tycon) then
            										let val existings = HashTable.lookup sumdatatypeTable tycon
            										in HashTable.insert sumdatatypeTable (tycon, (con, te_list) :: existings) end
            									else
            										HashTable.insert sumdatatypeTable (tycon, [(con, te_list)])
            								end
            							   ))
            	          	
            )))
        
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
		
    (* Creates a new frame for given expression of given type. *)
    (* desc is Exp.t. ty is Type_desc.t. *)
		fun expr_fresh desc ty = 
			if is_poly_instantiation desc then 
        (* unconstrained frame has Bottom refinement. *)
        Frame.fresh_unconstrained ty sumdatatypeTable 
			else 
        Frame.fresh ty sumdatatypeTable 
            
        (* lm as Lam {arg, argType, body = Exp {ty = bodyType, ...}, ...} *)
        (*
         *@param cstrs is the labeled_constraint
         *@param binding_table is the (pat, exp) binding definition table
         *@param call_deps is the (pat, pat) call dependencies list
         *@param binding_frame is the (pat, frame) binding frame definition table
         *@param paths is the path encoding of the program
         *@return a tuple of (fenv, cstrs, binding_table, call_deps, binding_frame)
         *)
        fun constrain_structure initfenv 
                                guard 
                                pdecs 
                                toplevelflag 
                                belong_pat 
                                freevars 
                                totalvars 
                                polymatching_table =
          let 
            val initial_size = 17
            val e_binding_table = HashTable.mkTable (hash_fn o (Var.toString) o pat_var, pat_eq) 
                                  (initial_size, Not_found)
            val e_binding_frame = HashTable.mkTable (hash_fn o (Var.toString) o pat_var, pat_eq) 
                                  (initial_size, Not_found)
            val e_call_deps = ref []
            val e_paths = ref []
            val e_insidefunbindings = HashTable.mkTable (hash_fn o (Var.toString) o pat_var, pat_eq) 
                                  (initial_size, Not_found)
            fun constrain_rec fenv  (*Init bindings*)
                              guard (*path guard. Empty list initially*)
                              cstrs (*CoreML.Dep.t list*)
                              binding_table 
                              call_deps (*ref []*)
                              binding_frame 
                              paths 
                              insidefunbindings 
                              pdecs 
                              toplevelflag 
                              belong_pat = 
            case pdecs of 
              [] => (fenv, cstrs, binding_table, call_deps, binding_frame, paths, insidefunbindings) 
            | (Dec.Datatype v) :: pdecs' => 
                (
                  cacheDataType v; 
                  constrain_rec fenv 
                                guard 
                                cstrs 
                                binding_table 
                                call_deps 
                                binding_frame paths 
                                insidefunbindings 
                                pdecs'
                                toplevelflag 
                                belong_pat
                )							     
            | (Dec.Exception ca) :: pdecs' => constrain_rec fenv 
                                                            guard 
                                                            cstrs 
                                                            binding_table 
                                                            call_deps 
                                                            binding_frame 
                                                            paths 
                                                            insidefunbindings 
                                                            pdecs' 
                                                            toplevelflag 
                                                            belong_pat
            | (Dec.Fun {decs, tyvars, ...}) :: pdecs' => 
                  let val recflag = ref false
                    val	bindings = Vector.toListMap (decs, (fn {lambda=lm, var=var'} 
                              => (
                                let val lm' = Lambda.dest lm
                                  val argType = #argType lm'
                                  val body = #body lm'
                                  val bodyType = Exp.ty body
                                  val _ = recflag := isRecursiveFun body var'; 
                                  val fpat = (Pat.var (var', Type.arrow (argType, bodyType)))
                                  val _ = if (toplevelflag) then () else 
                                    List.push (call_deps, (belong_pat, fpat))	
                                in	        									
                                  (fpat, (Exp.lambda lm))
                                end
                                 )))
                    in
                      let val (fenv, cstrs') 
                        = constrain_bindings fenv 
                                             guard 
                                             (!recflag) 
                                             bindings 
                                             toplevelflag 
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
                        constrain_rec fenv guard (cstrs @ cstrs') binding_table call_deps binding_frame paths insidefunbindings
                                    pdecs' toplevelflag belong_pat 
                      end
                    end					        	
                | (Dec.Val {rvbs, tyvars, vbs, ...}) :: pdecs' =>
                    let val recflag = ref false
                      val	bindings = Vector.toListMap (rvbs, (fn {lambda=lm, var=var'}
                                =>(
                                  let val lm' = Lambda.dest lm
                                    val argType = #argType lm'
                                    val body = #body lm'
                                    val bodyType = Exp.ty body
                                    val _ = recflag := isRecursiveFun body var'
                                    val fpat = (Pat.var (var', Type.arrow (argType, bodyType)))
                                    val _ = if (toplevelflag) then () else 
                                       List.push (call_deps, (belong_pat, fpat))
                                  in
                                    (fpat, (Exp.lambda lm))
                                  end
                                  )))
                    
                              @
                              (Vector.toListMap (vbs, (fn {exp=exp', pat=pat', ...} => (
                                (*if (toplevelflag) then () 
                                else (
                                  if (Type.isArrow (CoreML.Exp.ty exp')) then
                                    List.push (call_deps, (belong_pat, pat'))
                                  else ()
                                ); *)
                                case (Exp.node exp') of
                                  Exp.App _  =>	
                                    if (HashTable.inDomain insidefunbindings belong_pat) then
                                      HashTable.insert insidefunbindings (belong_pat, (HashTable.lookup insidefunbindings belong_pat) @ [(pat', exp')])
                                    else 
                                      HashTable.insert insidefunbindings (belong_pat, [(pat', exp')])
                                  | _ => ();
                                (pat', exp')
                              ))))
              in
                let val (fenv, cstrs') 
                  = constrain_bindings fenv guard (!recflag) bindings toplevelflag belong_pat binding_table call_deps binding_frame paths insidefunbindings 
                    freevars totalvars polymatching_table
                    in constrain_rec fenv guard (cstrs @ cstrs') binding_table call_deps binding_frame paths insidefunbindings
                                    pdecs' toplevelflag belong_pat 
                    end
                  end
          in 
            constrain_rec initfenv 
                           guard 
                           [] 
                           e_binding_table 
                           e_call_deps 
                           e_binding_frame 
                           e_paths 
                           e_insidefunbindings 
                           pdecs 
                           toplevelflag 
                           belong_pat 
          end
		  	
		and constrain_bindings env 
                           guard 
                           recflag 
                           bindings 
                           toplevelflag 
                           belong_pat 
                           binding_table 
                           call_deps 
                           binding_frame 
                           paths 
                           insidefunbindings 
                           freevars 
                           totalvars 
                           polymatching_table =
			case recflag of (* return Le.t*(Constraint.labeled_constraint list) *)
		  		  false => List.fold (
                        bindings, (* Pat.t*Exp.t list *)
                        (env, []), 
                        (constrain_and_bind guard 
                                            toplevelflag 
                                            belong_pat 
                                            binding_table 
                                            call_deps 
                                            binding_frame 
                                            paths 
                                            insidefunbindings 
                                            freevars 
                                            totalvars 
                                            polymatching_table
                        )
                     )
		  		| true =>
		  			let 
              val exprs = List.map (bindings, (fn (a, b) => b))
		  				val pats = List.map (bindings, (fn (a, b) => a))
		  				val bindings = List.map (bindings, (fn (p, e) => (p, e, expression_to_pexpr e)))
              (* We need to figure out all the frames' labels before we can properly bind them. *)
			    		val unlabeled_frames = List.map (exprs, (fn e => F.fresh (Type.toMyType (Exp.ty e)) sumdatatypeTable))
			    		val unlabeled_env = bind_all bindings unlabeled_frames env
			    		val (label_frames, _) = constrain_subexprs unlabeled_env 
                                                         guard 
                                                         exprs 
                                                         belong_pat 
                                                         pats 
                                                         binding_table 
                                                         call_deps 
                                                         binding_frame 
                                                         paths 
                                                         insidefunbindings 
                                                         freevars 
                                                         totalvars 
                                                         polymatching_table
			    			
			    		val binding_frames = List.map2 (unlabeled_frames, label_frames, (fn (a, b) => F.label_like a b))		            
			    		(* Redo constraints now that we know what the right labels are *)
			    		val bound_env = bind_all bindings binding_frames env
			    		val (found_frames, subexp_cstrs) = constrain_subexprs bound_env guard exprs 
			    				belong_pat pats	binding_table call_deps binding_frame paths	insidefunbindings freevars totalvars polymatching_table	
			    		fun make_cstr fc pat = lc {lc_cstr = fc, lc_orig = Loc NONE, lc_id = fresh_fc_id (), lc_binding = pat}
			    		fun build_found_frame_cstr_list (found_frame, binding_f, pat, cs) =
			      			make_cstr (WFFrame (bound_env, binding_f)) pat ::
			      			make_cstr (SubFrame (bound_env, guard, found_frame, binding_f)) pat :: cs
              val ret_cs = (List.fold3 (found_frames, binding_frames, pats, [], build_found_frame_cstr_list)) @ subexp_cstrs
              val _ = pprint_debug "constrain_bindings"
                                   (lcstrs_to_fcstrs ret_cs)
                                   env
                                   guard 
                                   belong_pat 
                                   call_deps 
                                   paths 
                                   polymatching_table

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
				if Pattern.is_deep pat then
			      Le.add (Var.mk_ident "pattern")
			        (B.mk_int [(Var.mk_ident "", Var.mk_ident "", Pattern.desugar_bind pat pexpr)])
			        env
			    else env
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
		  	
		and constrain_and_bind guard 
                          toplevelflag 
                          belong_pat 
                          binding_table 
                          call_deps 
                          binding_frame 
                          paths 
                          insidefunbindings 
                          freevars 
                          totalvars 
                          polymatching_table 
				((pat, e), (env, cstrs)) =
			let 
				val _ = (print "binding ... pat is "; print (CoreML.Pat.visitPat pat); print " exp is "; print (CoreML.visitExp e))
				val patty = Pat.ty pat
				(* returns true if rhs of binding is a function definition *)
				fun isPureFunction e ty =
					if (Type.isArrow ty) then
						case (Exp.node e) of
							Exp.App _ => false
							| _ => true
					else false
					 
				val (f, cstrs') = 
					if (isPureFunction e patty) then 
						constrainExp e 
                        (Lightenv.copy env) 
                        guard 
                        pat (* Being passed as belong_pat *)
                        binding_table 
                        call_deps 
                        binding_frame 
                        paths 
                        insidefunbindings
                        freevars 
                        totalvars 
                        polymatching_table 
						(* function: new belong_pat *) (* we give a copy of env because we may instantiate top level functions *)
					else if toplevelflag then 
							constrainExp e 
                          (Lightenv.copy env) 
                          guard 
                          pat 
                          binding_table 
                          call_deps 
                          binding_frame 
                          paths 
                          insidefunbindings 
                          freevars 
                          totalvars 
                          polymatching_table
					else constrainExp e 
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
                            polymatching_table (* non function: depend on toplevelflag *)
		  		val env = tbind env pat f (expression_to_pexpr e) 
		  	in 
		  		(if (toplevelflag orelse (isPureFunction e patty))
		  		then (HashTable.insert binding_table (pat, e); HashTable.insert binding_frame (pat, f))
		  		else ());
		  		(env, cstrs @ cstrs') 
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

	    and constrainExp e 
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
                       polymatching_table = 
			let 
        val _ = print ("Constraining Exp " ^ (CoreML.visitExp e) ^ "\n")
				val desc= (Exp.node e)
				val tyy = Type.toMyType (Exp.ty e)
        (* lo and behold, for a new frame is born! *)
				val environment = (env, guard, expr_fresh desc tyy) (*Note type is only among var, arrow, constr, record(tuple)*)
				val (f, cstrs, rec_cstrs) = 
					case desc of
              (   Exp.Const f) => constrain_constant (f())
		      			| (Exp.Con (c, targs)) => (case (Con.toString c) of
		      				  "true" => (Fconstr (Tycon.bool, [], Frame.fresh_true ()), [], [])
		      				| "false" => (Fconstr (Tycon.bool, [], Frame.false_refinement), [], []) 
		      				|_  => (print ("\nconstructor frame generating error"); assertfalse ()))  (* "nil", "ref" is not currently supported *)
		      			| Exp.Record r => constrain_record environment 
                                                   (Record.toVector(r)) 
                                                   belong_pat 
                                                   binding_table 
                                                   call_deps 
                                                   binding_frame 
                                                   paths 
                                                   insidefunbindings
                                                   freevars 
                                                   totalvars 
                                                   polymatching_table
		      			| Exp.Case {rules, test, ...} => constrain_match environment 
                                                                 test 
                                                                 (Vector.toListMap 
                                                                  (rules, (fn {exp, pat, ...} => (pat, exp))))
                                                                 belong_pat
                                                                 binding_table 
                                                                 call_deps 
                                                                 binding_frame 
                                                                 paths	
                                                                 insidefunbindings 
                                                                 freevars 
                                                                 totalvars 
                                                                 polymatching_table     
		      			| Exp.Var (var, targs) => constrain_identifier environment 
                                                               (var()) 
                                                               e 
                                                               freevars 
                                                               totalvars 
                                                               polymatching_table   
                (* All primary operators like <,>,<= etc are also Exp.App *)
		      			| Exp.App (e1, e2) => (case (Exp.node e1) of 
		      				  (Exp.Con (c, targs)) => 
		      					let
		      						val e2list = case (Exp.node e2) of Exp.Record e2 => (Vector.toListMap ((Record.toVector e2), (fn (a, b) => b)))
		      														| _ => [e2]
		      						val tycon1 = case tyy of Type_desc.Tconstr (tyc, _) => tyc | _ => (print "\nIll constructor\n"; assertfalse ()) 
		      						val tylist = HashTable.lookup datatypeTable c handle Not_found => [] (* built-in constructor *)
		      						val t = Tconstr (tycon1, tylist)
		      						val sumf = #3 environment
		      						val f = case sumf of
		      							Fsum (_, fs, _) => 
		      								let val f = List.peek (fs, fn (c', f) => Con.equals (c, c'))
		      									val f =  case f of SOME (_,f) => f | NONE => (print "\nIll type from a datatype\n"; assertfalse ())
		      								in Frame.unfoldRecursiveFrame f tycon1 fs end
		      							| Fconstr (tcc, fls, r) => 
		      								if (String.equals ("::", Con.toString c)) then Fconstr (tcc, (List.first fls :: fls), r) (* This is considered as unsafe *)
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
              | Exp.EnterLeave (e, si) => (print "We do not check EnterLeave"; assertfalse ())
              | Exp.Handle {catch, handler, try} => (print "We don not check Handle"; assertfalse ())
              | Exp.PrimApp {args, prim, targs} => (print "We do not check PrimApp"; assertfalse ())
              | Exp.Raise e => (print "We do not check Raise"; assertfalse ())
       		in 
       			log_frame e f; (f, (List.map (cstrs, (label_constraint e belong_pat))) @ rec_cstrs)
       		end
		
		and constrain_constant cons =
      let
        val cs = (case cons of 
		   		 Const.IntInf n => (
		   		 	(*print "\nIntInf\n";*)
		   		 	(B.mk_int [B.equality_qualifier (P.PInt (IntInf.toInt n))], [], []) (*==(f,cstrs,rec_cstrs)*)
		   		 	)
		       | Const.Null => (B.uUnit, [], [])
		       | Const.Real _ => (B.uFloat, [], [])
		       | Const.Word n => (
		       		(*print "\nWord\n";*)
		       		(B.mk_int [B.equality_qualifier (P.PInt (IntInf.toInt (WordX.toIntInfX n)))], [], [])
		       		)
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
							case f of Fconstr (_, fl, _) => fl | _ => (print ("\nConstructor with ill type " ^ (Frame.pprint f) ^ "\n"); assertfalse ())
						(* Seeking the actual types of args which are actuals *)
						val _ = print "go here0\n"
						val (argframes, argcstrs) = constrain_subexprs env guard args belong_pat [] (* not pats for them *) 
														binding_table call_deps binding_frame paths insidefunbindings freevars totalvars polymatching_table
						val _ = print "go here\n"
            val ret_cs = WFFrame(env, f) :: ((List.map2 (argframes, cstrargs, (fn (arg, formal) => SubFrame(env, guard, arg, formal)))) @ (lcstrs_to_fcstrs argcstrs))
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
			         WFFrame(env, f) :: (List.map2 (argframes, cstrargs, (fn (arg, formal) => SubFrame(env, guard, arg, formal)))),
			         argcstrs) end
			    | _ => assertfalse ()
		
		(* In this function, we first get the expression of all recored fields.
		 * Then we constrain this field expression
		 * Then we build refinements for this fiel expression
		 * Then we add subtyping contraints mainly for actual <: formal
		 *)
		and constrain_record (env, guard, f) 
                         labeled_exprs 
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
		   	  val labeled_exprs = QuickSort.sortVector ( 
                                labeled_exprs, 
                                (fn ((a, b), (a', b'))=> (Field.<= (a, a')))
                              )	 
		  	  val sorted_exprs = ((Vector.toList o (fn (a, b) => b)) (Vector.unzip labeled_exprs))
		  	  (*val _ = (print "TTTThe order of sorted exprs is \n\n" ; List.foldr (sorted_exprs, (), fn (a, b) => (print o CoreML.visitExp) a))*)
		      val (subframes, subexp_cs) = constrain_subexprs env 
                                                          guard 
                                                          sorted_exprs 
                                                          belong_pat 
                                                          [] (* no pats for them *)
                                                          binding_table 
                                                          call_deps 
                                                          binding_frame 
                                                          paths 
                                                          insidefunbindings 
                                                          freevars 
                                                          totalvars 
                                                          polymatching_table
          (* Individual frames for record fields must match 
             corresponding frames of sub-expressions *)
		      fun subframe_field (fsub, (fsup, _), cs_rest) = (SubFrame (env, guard, fsub, fsup)) :: cs_rest 
		  in
			  case f of
			  	F.Frecord (recframes, _) => 
			      let 
              fun field_qualifier ((_, name), fexpr) = B.field_eq_qualifier name (expression_to_pexpr fexpr) 
              (* In case of tuples, names are "1", "2".. So, qualifier would
                 be x11.1 = pfexp1, x11.2 = pfexp2...*)
              val ret_f = F.Frecord (recframes, ([], F.Qconst (List.map2 (recframes, sorted_exprs, field_qualifier))))
              val (cur_cs : frame_constraint list) = WFFrame (env, f) :: List.fold2 (subframes, recframes, [], subframe_field)
              val (slist : frame_constraint list) = lcstrs_to_fcstrs subexp_cs
              val ret_cs = cur_cs@slist
              val _ = pprint_debug "constrain_record"
                                   (ret_cs)
                                   env
                                   guard 
                                   belong_pat 
                                   call_deps 
                                   paths 
                                   polymatching_table
			      in
			        (ret_f, cur_cs, subexp_cs)
			      end
			    | _ => assertfalse ()
		   end
		   
		   	
		(* matchf is the frame of the test condition while matche is the Predicate.pexpr ofthe test condition *)
		and constrain_case (env, guard, f) 
                        matchf 
                        matche (* pexpr list *)
                        belong_pat 
                        binding_table 
                        call_deps 
                        binding_frame 
                        paths 
                        insidefunbindings 
                        freevars 
                        totalvars 
                        polymatching_table 
                        (guardvar, i, (pat, e)) =
			let 
        (* guard updated with correct guard value *)
				val guard = (guardvar, i, true) :: guard
        val _ = print ("Before matchcase_tbind, pat is "^(CoreML.Pat.visitPat pat)^" and pexpr is "^(P.pprint_pexpr matche)^"\n")
				val env = matchcase_tbind env pat matchf matche
        (* Now, env contains mapping bewteen  
           1. pat frame and matchf
           2. forevery pat' inside pat and
                for corresponding pexpr' inside matche
                  pat' -> pexpr'
         *)
				val (fe, subcs) = constrainExp e 
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
        (* generated constraints refer to extended env and updated guard *)
        val ret_cs = (SubFrame (env, guard, fe, f))::(lcstrs_to_fcstrs subcs)
        val _ = pprint_debug "constrain_case"
                             ret_cs
                             env
                             guard 
                             belong_pat 
                             call_deps 
                             paths 
                             polymatching_table
        
			in (SubFrame (env, guard, fe, f), subcs) end
		
		(* e is the test; pexps are paris of (pat, exp) *)
		and constrain_match (environment as (env, guard, f)) 
                        e (* this is test *)
                        pexps (* (pat,expr) list *)
                        belong_pat 
                        binding_table 
                        call_deps 
                        binding_frame 
                        paths 
                        insidefunbindings 
                        freevars 
                        totalvars 
                        polymatching_table =
			if (Type.isBool (Exp.ty e)) then
				let 
          val _ = print ("Constaining bool expression : "^(CoreML.visitExp e)^"\n")
          val (f1, cstrs1) = constrainExp e 
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
          (* guardvar creation site. we have 2 cases *)
					val guardvar = Var.mk_ident "guard"
					
					val (f1, guard2, guard3) = case f1 of 
              (* v1 : ">=", v2 : Var(z), v3 : pexpr *)
              F.Fconstr (a, b, (subs,F.Qconst[(v1,v2,P.Iff (v3,p))])) => 
                (f1, (guardvar, 1, true) :: guard, (guardvar, 0, true) :: guard)
						| F.Fconstr (a, b, (subs, F.Qconst [(v1, v2, P.Atom (v3, P.Eq, bf))])) => 
							let 
                val pd = P.big_and [P.Atom (v3, P.Eq, bf), P.Atom (v3, P.Lt, P.PInt 2), P.Atom (v3, P.Ge, P.PInt 0)]
                (* 1. Are there any int operations with bool return type which have 
                      equality in their refinement?
                   2. Why is 0<v3<2 ?  
                 *)
							in 
                print ("\nBool frame being examined is "^(F.pprint f1)^"\n");
                (F.Fconstr (a, b, (subs, F.Qconst [(v1, v2, pd)])), (guardvar, 1, false) :: guard, (guardvar, 0, false) :: guard) 
              end
						| _ => (print ("Error: if-then-else branching condition ill formed" ^ (Frame.pprint f1)); assertfalse ())	
						
          (* We extend the environment with the frame of bool test 
             We create a guardvar g and associate the frame to g. So env contains g -> f
             guard_t array associates g to an integer describing current case.
           *)
					val env' = Le.add guardvar f1 env 
				      (* fli : frame for entire case-rules, cli - constraons for entire case-rules *)		
					val (subflist, subclist) = List.fold (pexps, ([], []), (fn ((p, e), (fli, cli)) => case (Pat.node p) of 
											  Pat.Con {arg=arg',con=con',targs=targs'} => (
											  	(case Con.toString (con') of
											  		  "true" => let 
                                          val (f2, cstrs2) = constrainExp e 
                                                                          env' 
                                                                          guard2 
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
                                          (* frame for each case match => frame of case-expr *)
                                          (SubFrame(env', guard2, f2, f) :: fli, cstrs2 @ cli) 
                                          (* true <=> (f2 => f) *)
                                        end
											  		| "false" => let 
                                            val (f3, cstrs3) = constrainExp e 
                                                                            env' 
                                                                            guard3 
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
                                           (SubFrame(env', guard3, f3, f) :: fli, cstrs3 @ cli) 
                                         end 
											  		| _ => (print "generating constraints for if-else error1"; assertfalse ())))
											| _ => (print "generating constraints for if-else error2"; assertfalse ())))
					(*val _ = print ("\nNow Listpushing the " ^ (Var.toString (pat_var belong_pat)) ^ "ifelsethen branch\n")*)
					val _ = case f1 of 
						F.Fconstr (a, b, (subs,F.Qconst[(v1,v2,P.Iff (v3,p))])) => 
							if Predicate.logic_equals_pexp v3 (B.tag (P.PVar v2)) then 
                (* If v3 and v2 refer to same program variable. then  add predicate p to path info*)
                                            (* FunApp("__tag",[Var("guard158")]) *)
                (* path encoded as belong_pat*guardvar*(corresponding predicate)*bool *)
								List.push (paths, (belong_pat, (B.tag (P.PVar guardvar)), (Predicate.apply_substs subs p), false))
							else (print "Error: if-else-then unknown frame encountered."; assertfalse ())
						| F.Fconstr (_, _, (_, F.Qconst [(_, _, _)])) => 
							List.push (paths, (belong_pat, ((P.PVar guardvar)), P.True, false))
						| _ => (print ("Error: if-then-else branching condition ill formed" ^ (Frame.pprint f1)); assertfalse ())		
          val ret_cs = (WFFrame(env, f) :: subflist) @ (lcstrs_to_fcstrs (cstrs1 @ subclist))
          val _ = pprint_debug "constrain_match - if-then-else"
                               (ret_cs)
                               env'
                               guard 
                               belong_pat 
                               call_deps 
                               paths 
                               polymatching_table
				in
					(f, WFFrame(env, f) :: subflist, cstrs1 @ subclist)
				end
			else 
        (* not a boolean expression *)
				let 
          (* frame and cstrs for case test expr *)
					val (matchf, matchcstrs) = constrainExp e 
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
					val cases_size = List.length pexps
					val v1 = Var.mk_ident ""
					val v2 = Var.mk_ident "" 
					val p1 = P.Atom (B.tag (P.PVar v2), P.Lt, (P.PInt cases_size)) 
					val p2 = P.Atom (B.tag (P.PVar v2), P.Ge, (P.PInt 0)) 
					val q = (v1, v2, P.And (p1, p2))
          (* Only Integer type constr *)
					val f1 = F.Fconstr(Tycon.defaultInt (), [], ([], Qconst [q]))
          (* Here comes the guardvar *)
          (* guardvar is int-tagged to enumerate cases *)
					val guardvar = Var.mk_ident "guard"
          (* env is extended with (guardvar -> test_frame) mapping *)
          val env' = Le.add guardvar f1 env
					val environment = (env', guard, f)
					val cases = List.mapi (pexps, fn (i, (pat, e')) => (constrain_case environment 
                                                                              matchf 
                                                                              (matchcase_exp_to_pexpr e) 
                                                                              belong_pat 
                                                                              binding_table 
                                                                              call_deps 
                                                                              binding_frame 
                                                                              paths 
                                                                              insidefunbindings 
                                                                              freevars 
                                                                              totalvars 
                                                                              polymatching_table 
                                                                              (guardvar, i, (pat, e'))))
					(*val _ = print ("\nNow Listpushing the " ^ (Var.toString (pat_var belong_pat)) ^ " guad " ^ (Var.toString guardvar) ^ " case\n")
					val _ = print "\nend casing\n"*)
					val cstrs = List.map (cases, (fn (a, b) => a))
					val subcstrs = List.map (cases, (fn (a, b) => b))
          (* path updated *)
					val _ = List.push (paths, (belong_pat, (B.tag (P.PVar guardvar)), Predicate.True, false))
          val ret_cs = (WFFrame (env, f) :: cstrs) @ (lcstrs_to_fcstrs (List.concat (matchcstrs::subcstrs)))
          val _ = pprint_debug "constrain_match - non bool"
                               (ret_cs)
                               env'
                               guard 
                               belong_pat 
                               call_deps 
                               paths 
                               polymatching_table
				in 
          (f, WFFrame (env, f) :: cstrs, List.concat (matchcstrs :: subcstrs)) 
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
              val ret_cs = [WFFrame (env, f), SubFrame (env', guard, f'', f')] @ (lcstrs_to_fcstrs cstrs)
              val _ = pprint_debug "constrain_lambda"
                                   (ret_cs)
                                   env
                                   guard 
                                   belong_pat 
                                   call_deps 
                                   paths 
                                   polymatching_table
				    in
				    	(f, [WFFrame (env, f), SubFrame (env', guard, f'', f')], cstrs)
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
                 (f, [WFFrame(env, f)], []) 
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
                          (* Fconstr(TyCon.bool,[], (sublist,Qcons[(Var(">="),Var(z),pred)])) 
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
              val ret_cs = (SubFrame (env, guard, f2, f) :: cstrs)@(lcstrs_to_fcstrs (e2_cstrs @ subexp_cstrs))
              val _ = pprint_debug "constrain_application - apply_once"
                                   (ret_cs)
                                   env
                                   guard 
                                   belong_pat 
                                   call_deps 
                                   paths 
                                   polymatching_table
            in 
              (f'', SubFrame (env, guard, f2, f) :: cstrs, e2_cstrs @ subexp_cstrs) 
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
          val (env', cstrs1, binding_table', call_deps', binding_frame', paths', insidefunbindings') = 
						constrain_structure env 
                                guard 
                                decs 
                                false 
                                belong_pat 
                                freevars 
                                totalvars 
                                polymatching_table (* not in the toplevel*)
          (* let bindings only extend the environment. So we pass
             extended env to constrain body. However, constraints generated
             inside above call refer to correct (updated) guard_t *)
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
				      Exp.Let (_, _) => (body_frame, [WFFrame (env, body_frame)], cstrs1 @ cstrs2)
				    | _ =>
				      let (*val _ = print "\nbefore labelling\n"*) 
				          val f = F.label_like f body_frame
				          (*val _ = print "\nend labelling\n" *)
                  val ret_cs = ([WFFrame (env, f), SubFrame (env', guard, body_frame, f)])@(lcstrs_to_fcstrs (cstrs1 @ cstrs2))
                val _ = pprint_debug "constrain_let"
                                     (ret_cs)
                                     env
                                     guard 
                                     belong_pat 
                                     call_deps 
                                     paths 
                                     polymatching_table
				      in
				      	(f, [WFFrame (env, f), SubFrame (env', guard, body_frame, f)], cstrs1 @ cstrs2)
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
		  		fun mksub b a = SubFrame(env, guard, a, b) 
		  	in
		    	(f, WFFrame(env, f) :: List.map (mksub (List.first fs)) fs', sub_cs)
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
        fun mksub b a = SubFrame(env, guard, a, b) 
      in
        (f, WFFrame(env, f) :: List.map (fs', (mksub (List.first fs))), sub_cs)
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
        val ret_cs = [SubFrame (env, guard, B.mk_int [], B.mk_int [assert_qualifier])] @ (lcstrs_to_fcstrs cstrs)
        val _ = pprint_debug "constrain_assert"
                             (ret_cs)
                             env
                             guard 
                             belong_pat 
                             call_deps 
                             paths 
                             polymatching_table
		  	in 
          (B.mk_unit (), [SubFrame (env, guard, B.mk_int [], B.mk_int [assert_qualifier])], cstrs) 
        end
		
		
		fun simplylc c = case c of
			  lc c' => c'
			  										    
		structure QualifierSet = ListSetFn (open Qualifier)
		


		(* Make copies of all the qualifiers where the free identifiers are replaced
		   by the appropriate bound identifiers from the environment. *)
		fun instantiate_in_environments cs qs =
			(* Collect all keys (i.e. variable name?) in the env in all cs'(constraints) *)
			let val domains = List.map (cs, (fn c => case #lc_cstr (simplylc c) of 
														SubFrame (e,_,_,_) => Lightenv.domain e | WFFrame (e,_) => Lightenv.domain e))
				
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
			        Loc exp =>
				        (case #lc_cstr cstr' of
				            SubFrame (_, _, f1, f2) =>
				            	(exp, NotSubtype (F.apply_solution s f1,  F.apply_solution s f2))
				          | WFFrame (_,f) => (exp, IllFormed (F.apply_solution s f)))
			      | Assert exp => (SOME exp, AssertMayFail)
			      | Cstr cstr => error_rec (simplylc cstr)
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
		    in SOME (SubFrame (fenv, [], f', F.label_like f f')) end
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
