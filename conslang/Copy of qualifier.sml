signature QUALIFIER_STRUCTS = 
	sig
		include ATOMS
		structure Predicate : PREDICATE
	    sharing type Predicate.Var.t = Var.t
	end


signature QUALIFIER (*: ORD_KEY*) = 
	sig
		include QUALIFIER_STRUCTS
		
		(* The first is this qualifer's name; second is the referred variable in the program text; third is its shape *)
		type t = Var.t * Var.t * Predicate.t
		(* pending substitution is pushed in *)
		val apply: Predicate.pexpr -> t -> Predicate.t
		(* give unique representation to variables in the predicate *)
		val instantiate: (string * Var.t) list -> t -> t option
		(* val pprint: formatter -> t -> unit *)
		
		val transl_pattern_qual : PATQualifier.t -> t list
		
		val logic_equals : t -> t -> bool
		
		val parse : PATQualifier.t list -> t list
	end

functor Qualifier (S : QUALIFIER_STRUCTS) : QUALIFIER = 
	struct
		open S
	
		open Predicate
		
		type t = Var.t * Var.t * Predicate.t
		
		type ord_key = t

    	fun compare (q1, q2) = String.compare (Var.toString q1, Var.toString q2)
		
		(* let pprint ppf (_, _, pred) = Predicate.pprint ppf pred *)
		
		fun apply x (_, y, p) = Predicate.subst x y p
		
		exception Refinement_not_closed
		
		fun instantiate varmap (path, valu, pred) =
		  let val varmap = (Var.toString valu, valu) :: varmap 
		  in
		  	(SOME (path, valu, Predicate.instantiate_named_vars varmap pred))
		    handle Common.Not_found => NONE
		  end
		  
		fun transl_pattern_qual patq = 			
			Predicate.transl_pattern_pred patq
			
		fun logic_equals (qname1, v1, p1) (qname2, v2, p2) =
			Var.logic_equals (qname1, qname2) andalso Var.logic_equals (v1, v2) andalso (Predicate.logic_equals p1 p2)
		
		
		fun parse result = Common.flap (fn q => transl_pattern_qual q) result
	end