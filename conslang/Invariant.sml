signature INVARIANT = 
	sig
		include ATOMS
		
		type t = Var.t * Var.t * Predicate.t
		
		val transl_pattern_qual : PATInvariant.t -> t list
	
		val parse : PATInvariant.t list -> t list
	end

structure Invariant : INVARIANT = 
	struct
		open Atoms
		
		type t = Var.t * Var.t * Predicate.t
		
		fun transl_pattern_qual patinv = 			
			Predicate.transl_pattern_pred patinv
			
		fun parse result = Common.flap (fn inv => transl_pattern_qual (PATInvariant.translate inv)) result
	end