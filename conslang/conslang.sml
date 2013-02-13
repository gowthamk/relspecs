signature CONSLANG_STRUCTS = 
	sig
		include ATOMS
	end

signature CONSLANG = 
	sig
		structure Predicate : PREDICATE
		structure Qualifier : QUALIFIER
		structure RelPredicate : REL_PREDICATE
		structure RelQualifier : REL_QUALIFIER
	end

functor Conslang (S : CONSLANG_STRUCTS) : CONSLANG = 
	struct
		structure Predicate = Predicate (open ATOMS)
		structure Qualifier = Qualifier (open ATOMS structure Predicate = Predicate)
		structure RelPredicate = RelPredicate (open ATOMS)
		structure RelQualifier = RelQualifier (open ATOMS)
	end
