
signature REL_QUALIFIER (*: ORD_KEY*) = 
	sig
		include ATOMS
		
		(* The first is this qualifer's name; second is the referred variable in the program text; third is its shape *)
		type t = Var.t * RelPredicate.typedvar* RelPredicate.t
    val mk_true : unit -> t

		val equality_qualifier : Con.t ->  RelPredicate.rexpr -> t
		val subset_qualifier : Con.t ->  RelPredicate.rexpr -> t
		(* pending substitution is pushed in *)
		(*val apply: RelPredicate.rexpr -> t -> RelPredicate.t*)
		(* give unique representation to variables in the predicate *)
		val instantiate: (string * Var.t) list -> t -> t option
		
		val pprint: t -> string
		
		(*val transl_pattern_qual : PATQualifier.t -> t list
		
		val logic_equals : t -> t -> bool
		
		val parse : PATQualifier.t list -> t list*)
	
	end

structure RelQualifier : REL_QUALIFIER = 
	struct
		open Atoms

    structure RP = RelPredicate
	
		type t = Var.t * Var.t * RelPredicate.t

    fun mk_true () = (Var.dummy (), Var.mk_ident "rtrue", RelPredicate.RTrue)
		
		fun equality_qualifier con exp =
			let 
        val x = Var.mk_ident "V" 
        val tyv = RP.make_typedvar(x)
				val rpred = RP.requals (RP.make_rrel (con,tyv)) exp
		   		val expstr = RP.pprint rpred 
		   	in (Var.mk_ident expstr, tyv, rpred) end

		fun subset_qualifier con exp =
			let 
        val x = Var.mk_ident "V" 
        val tyv = RP.make_typedvar(x)
				val rpred = RP.rsub (RP.make_rrel (con,tyv)) exp
		   		val expstr = RP.pprint rpred 
		   	in (Var.mk_ident expstr, tyv, rpred) end

    fun pprint (v,bv,pred) = "Q("^(Var.toString bv)^")"^
      " :: "^(RP.pprint pred)


		(*type ord_key = t

    	fun compare ((v1, v2, p), (v1', v2', p')) = 
    		let 
    			val str = (Var.toString v1) ^ (Var.toString v2) ^ (RelPredicate.pprint p)
    			val str' = (Var.toString v1') ^ (Var.toString v2') ^ (RelPredicate.pprint p')
    		in	
    			String.compare (str, str')
    		end
		
		(* let pprint ppf (_, _, pred) = Predicate.pprint ppf pred *)
		
		fun apply x (_, y, p) = Predicate.subst x y p
		
		exception Refinement_not_closed *)
		
    (* Instantiate ALL variables in predicate with real program vars *)
		fun instantiate varmap (path, valu, rpred) =
		  let val varmap = (Var.toString valu, valu) :: varmap 
		  in
		  	(SOME (path, valu, RelPredicate.instantiate_named_vars varmap rpred))
		    handle Common.Not_found => NONE
		  end
		  
		(*fun transl_pattern_qual patq = 			
			Predicate.transl_pattern_pred patq
			
		fun logic_equals (qname1, v1, p1) (qname2, v2, p2) =
			Var.logic_equals (qname1, qname2) andalso Var.logic_equals (v1, v2) andalso (Predicate.logic_equals (p1, p2))
		
		
		fun parse result = Common.flap (fn q => transl_pattern_qual q) result
		
		fun pprint (v1, v2, p) = "qualf v1: " ^ (Var.toString v1) ^ " v2: " ^ (Var.toString v2) ^ " predicate: " ^ (Predicate.pprint p) 
		*)
	end
