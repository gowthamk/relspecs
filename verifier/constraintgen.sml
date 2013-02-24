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
		  			| (Exp.Con (c, targs), _) => 
              let
                val expty = Type.toMyType (Exp.ty e)
                val _ = print ("Type of args of "^(Con.toString c)^" : "^
                        (CoreML.visitType (Exp.ty e2))^"\n")
                val _ = print ("Whereas type of e1 e2 is "^(CoreML.visitType (Exp.ty e))^"\n")
                val _ = print ("And targs are \n")
                val _ = Vector.toListMap (targs,(fn t => (print ((CoreML.visitType t)^"\n"))))
                fun getArgTypes e2 = (case Type.toMyType(Exp.ty e2) of
                    Ttuple tdl => List.map (tdl, 
                      (fn tf => (case tf of (Tfield(_,t)) => t|_=>(print "Non-tfield inside tconstr\n";assertfalse()))))
                  | any => [any]
                )
                val tdl = getArgTypes e2
                val ilist = List.foldi(tdl,[],
                  (fn (i,t,l) => if(Type_desc.sametype(t,expty))then 
                      (l@[i]) 
                    else (l)))
                val _ = print ("For expression : "^(CoreML.visitExp e2)^", indexes : \n")
                val _ = List.fold(ilist,(),(fn(i,_)=>(print(Int.toString(i)))))
              in
                 Predicate.FunApp (Con.toString c, [expression_to_pexpr e2])
              end
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
		  
	end
