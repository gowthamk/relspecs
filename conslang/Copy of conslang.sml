signature CONSLANG_STRUCTS = 
	sig
		include ATOMS
	end

signature CONSLANG = 
	sig
		structure Predicate : PREDICATE
		structure Qualifier : QUALIFIER
	end

functor Conslang (S : CONSLANG_STRUCTS) : CONSLANG = 
	struct
		structure Predicate = Predicate (open ATOMS)
		structure Qualifier = Qualifier (open ATOMS structure Predicate = Predicate)
	end