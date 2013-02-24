signature PATTERN = 
	sig
		include ATOMS
		val is_deep : CoreML.Pat.t -> bool
		val pattern_extend : CoreML.Pat.t option -> CoreML.Pat.t list
		val bind_vars : CoreML.Pat.t -> CoreML.Pat.t -> (Var.t * Var.t) list
		val bind_pexpr : CoreML.Pat.t -> Predicate.pexpr -> (Var.t * Predicate.pexpr) list
		val desugar_bind : CoreML.Pat.t -> Predicate.pexpr -> Predicate.t
		val desugar_rbind : CoreML.Pat.t -> RelPredicate.rexpr ->
      TyconMap.t -> RelPredicate.t
    val bind_relem : CoreML.Pat.t -> RelPredicate.relem list -> (Var.t*RelPredicate.relem) list
		val same : (CoreML.Pat.t * CoreML.Pat.t) -> bool
		val vars : CoreML.Pat.t -> Var.t list
	end
	
structure Pattern : PATTERN = 
	struct
		open Atoms
		structure P = Predicate
    structure RP = RelPredicate
		structure C = Common
		structure TM = TyconMap
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

    fun pat_to_rexpr pat tm = case CoreML.Pat.node pat of
        CoreML.Pat.Con {arg=NONE,con=c,targs=targv} => SOME (RP.make_null_rset())
      | CoreML.Pat.Con {arg=SOME pat',con=c,targs=targv} => 
        let
          val flags = List.map ((TM.get_argtys_by_cstr tm c), (fn(x,y)=>y)) 
          fun atoms_to_rexpr pat flag (l1,l2) = (case CoreML.Pat.node pat of
              CoreML.Pat.Const constf => 
              let
                 val constval = ( case constf() of 
                     Const.IntInf n => (IntInf.toInt n)
                   | Const.Word n => (WordX.toInt n)
                   | _ => (print "Only int consts are allowed\n"; assertfalse ()))
              in
               ((RP.RInt constval)::l1,l2)
              end
            | CoreML.Pat.Var var => 
              if (flag) then
                (l1,(RP.make_rrel(c,RP.make_typedvar(var)))::l2)
              else
                ((RP.make_rvar (RP.make_typedvar var))::l1,l2)
            | _ => (print "not atom\n";assertfalse()))
          (*l1:relem list; l2:rexpr list*)
          val (l1,l2) = (case CoreML.Pat.node pat' of
              CoreML.Pat.Const _ => atoms_to_rexpr pat' false ([],[])
            | CoreML.Pat.Var _ => 
                (asserti ((List.length flags = 1),"cons args mismatch\n");
                atoms_to_rexpr pat' (List.first flags) ([],[]))
            | CoreML.Pat.Record pat_rec => 
              let
                val rpat_list = Vector.toListMap ((Record.toVector pat_rec),snd)
                val _ = asserti ((List.length rpat_list = List.length flags),
                  "Recorded constructor args pattern not agree\n")
              in
                List.fold2 (rpat_list,flags,([],[]),(fn(a,b,c) => (atoms_to_rexpr a b c)))
              end
            | _ =>(print "Invalid constructor args in pattern\n";assertfalse()) 
          )
        in
          SOME (RP.make_runion ((RP.make_rset l1)::l2))
        end
      | _ => NONE
		
		fun desugar_bind pat pexp =
		  P.big_and (List.map ((bind_pexpr pat pexp), (fn (x, exp) => P.equals (P.PVar x) exp)))

    (* An ideal way of binding patterns like tuples, records etc is by 
       making use of pexprs. *)
    fun bind_relem pat (relemlist : RP.relem list) = case (CoreML.Pat.node pat,relemlist) of
        (CoreML.Pat.Var var, [relem]) => [(var,relem)]
      | (CoreML.Pat.Record recrd,_) =>
        let
          val varlist = Vector.toListMap ((Record.toVector recrd),snd)
          val _ = asserti ((List.length varlist = List.length relemlist),
            "bind_relem error\n")
          val sublist = List.fold2(varlist,relemlist,[],
            (fn(p,r,l)=>l@(bind_relem p [r])))
        in
          sublist
        end
      | _ => fail "Only variables and records allowed\n"
      
		fun desugar_rbind pat rexpr tm =
      let
        val pat_rexpr = pat_to_rexpr pat tm
      in
        case pat_rexpr of
          SOME r => RP.requals r rexpr
        | NONE => RP.RTrue
      end

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
