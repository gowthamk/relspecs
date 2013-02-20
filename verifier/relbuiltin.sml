signature REL_BUILTIN = 
	sig			
		include ATOMS
		
		val translated_name : (string, string) HashTable.hash_table
		
		val retranslated_name : (string, string) HashTable.hash_table
		
		val qsize_arr : Predicate.binrel -> Var.t -> Var.t -> Var.t -> Qualifier.t
		
		val qsize_str : Predicate.binrel -> Var.t -> Var.t -> Var.t -> Qualifier.t
		
		val mk_int : Qualifier.t list -> RelFrame.t
		val mk_string : Qualifier.t list -> RelFrame.t
		val mk_bool : Qualifier.t list -> RelFrame.t
		val mk_array : RelFrame.t -> Qualifier.t list -> RelFrame.t
		val mk_unit : unit -> RelFrame.t
		
		val uInt : RelFrame.t
		val uString : RelFrame.t
		val uBool : RelFrame.t
		val uUnit : RelFrame.t
		val uFloat : RelFrame.t
		val uChar :Frame.t
		
		val rInt : string -> Var.t -> Predicate.t -> RelFrame.t
		val rString : string -> Var.t -> Predicate.t -> RelFrame.t
		val rBool : string -> Var.t -> Predicate.t -> RelFrame.t
		val rArray : RelFrame.t -> string -> Var.t -> Predicate.t -> RelFrame.t
		
		
		val tag : Predicate.pexpr -> Predicate.pexpr
		
		val tag_function : string
		
		val frames : unit -> (Var.t * RelFrame.t) list
    
		val equality_qualifier : Type_desc.type_desc -> Con.t ->  RelPredicate.rexpr -> RelQualifier.t

		val and_frame : Predicate.t -> Predicate.t -> RelFrame.t 
		
		val or_frame : Predicate.t -> Predicate.t -> RelFrame.t
	end

structure RelBuiltin (*: BUILTIN*) =
	struct
		open Atoms
		open Qualifier
		(*open Predicate*)
    open RelPredicate
		open CoreML
		(*open Frame*)
		open RelFrame
		open Common
		open Smlsys
		
		(* For array length constraint, y == z in this case *)
		(*
    fun qsize funm rel x y z = (Var.mk_ident ("SIZE_" ^ (pprint_rel rel)), y,
		                       Atom(Predicate.PVar z, rel, FunApp(funm, [Predicate.PVar x])))
		
		fun qsize_arr rel x y z = qsize (HashTable.lookup translated_name "Array.length") rel x y z
		fun qsize_str rel x y z = qsize (HashTable.lookup translated_name "String.length") rel x y z
		
		fun qdim_row_arr rel x y z =  qsize ("nRows_0") rel x y z
		fun qdim_col_arr rel x y z =  qsize ("nCols_0") rel x y z
		
		fun qint rel i y =
		  (Var.mk_ident ("INT_" ^ (pprint_rel rel) ^ (Int.toString i)), y, Atom(Predicate.PVar y, rel, PInt i))
		
		fun qrel rel x y =
		    (Var.mk_ident ("_" ^ (Var.toString x) ^ (pprint_rel rel) ^ (Var.toString y) ^ "_"), 
		     x,
		     Atom(Predicate.PVar x, rel, Predicate.PVar y))
	  *)	
    fun mk_poly qs = RFvar (Var.mk_ident "a", ([],RQconst qs))
		fun mk_int qs = RFconstr(Tycon.defaultInt (), [], ([], RQconst qs))
		fun mk_string qs = RFconstr(Tycon.vector, [(RFconstr(Tycon.defaultChar (), [], ([], RQconst [])))], ([], RQconst qs)) (* string is a char vector *)
		fun mk_bool qs = RFconstr(Tycon.bool, [], ([], RQconst qs))
		fun mk_array rf qs = RFconstr(Tycon.array, [rf], ([], RQconst qs))
		fun mk_list rf qs = RFconstr(Tycon.list, [rf], ([], RQconst qs))
		fun mk_record rfs qs = RFrecord (rfs, ([], RQconst qs))
		fun mk_unit () = RFrecord ([], RelFrame.empty_refinement) (*Fconstr(Tycon.vector, [], ([], Qconst []))*)
		fun mk_ref rf qs = RFconstr(Tycon.reff, [rf], ([], RQconst qs))
		
		val uFloat = RFconstr(Tycon.defaultReal (), [], ([], RQconst []))
		val uChar = RFconstr(Tycon.defaultChar (), [], ([], RQconst []))
		val uString = mk_string []
		val uBool = mk_bool []
		val uInt = mk_int []
		val uUnit = mk_unit ()
    val uPoly = mk_poly []
		
		fun rString name v p = mk_string [(Var.mk_ident name, v, p)]
		fun rBool name v p = mk_bool [(Var.mk_ident name, v, p)]
		fun rInt name v p = mk_int [(Var.mk_ident name, v, p)] (* v: variable (Var.t). p: predicate *)
		fun rArray b name v p = mk_array b [(Var.mk_ident name, v, p)]
		
		val char = ref 0
		
		fun reset_idents () = (char := ((Char.ord #"a") - 1))
		
		fun fresh_ident () = (incr char; Char.toString (Char.chr (!char)))
		
    (* f: Var.t -> (Frame.t *(Var.t -> RelFrame.t)) *)
    (* function that takes single argument.
       1. Pat.t is for pattern of argument (tuple, record...)
       2. The two RelFrame.t for frames of argument and return val
    *)
		fun def f =
			let val (x, y) = (Var.fromString (fresh_ident ()), Var.fromString (fresh_ident ()))
		  		val (f, fy) = f x
			in RFarrow (SOME (Pat.var (x, Type.var(Tyvar.newNoname {equality = false}))), f, fy y) end
			
    (* Two arg (uncurried) function.*)
    (* Tuple treated as record wrt frames *)
    (* 1. Frecord frame has empty refinement since record itself
          has no refinement 
       2. Above frame serves as argument frame within frame for
          the function
    *)
		fun def2 f = 
			let val (x, y, z) = (Var.fromString (fresh_ident ()), Var.fromString (fresh_ident ()), Var.fromString (fresh_ident ()))
				val (f1, fy) = f x 
				val (f2, fz) = fy y
				val f'' = fz z
				val i = Pat.var (x, Type.var(Tyvar.newNoname {equality = false}))
				val j = Pat.var (y, Type.var(Tyvar.newNoname {equality = false}))
				val pat = Pat.tuple (Vector.new2 (i, j))				
			in				
				RFarrow (SOME pat, RFrecord([(f1, "1"), (f2, "2")], RelFrame.empty_refinement), f'') 
			end
		
		fun def3 f = 
			let val (x, y, z, a) = (Var.fromString (fresh_ident ()), Var.fromString (fresh_ident ()), Var.fromString (fresh_ident ()), Var.fromString (fresh_ident ()))
				val (f1, fy) = f x 
				val (f2, fz) = fy y
				val (f3, fa) = fz z
				val f'' = fa a
				val i = Pat.var (x, Type.var(Tyvar.newNoname {equality = false}))
				val j = Pat.var (y, Type.var(Tyvar.newNoname {equality = false}))
				val k = Pat.var (z, Type.var(Tyvar.newNoname {equality = false}))
				val pat = Pat.tuple (Vector.new3 (i, j, k))				
			in				
				RFarrow (SOME pat, RFrecord([(f1, "1"), (f2, "2"), (f3, "3")], RelFrame.empty_refinement), f'') 
			end
			
		fun def4 f = 
			let val (x, y, z, r, a) = 
					(Var.fromString (fresh_ident ()), 
					 Var.fromString (fresh_ident ()), 
					 Var.fromString (fresh_ident ()), 
					 Var.fromString (fresh_ident ()),
					 Var.fromString (fresh_ident ()))
				val (f1, fy) = f x 
				val (f2, fz) = fy y
				val (f3, fa) = fz z
				val (f4, fr) = fa a
				val f'' = fr r
				val i = Pat.var (x, Type.var(Tyvar.newNoname {equality = false}))
				val j = Pat.var (y, Type.var(Tyvar.newNoname {equality = false}))
				val k = Pat.var (z, Type.var(Tyvar.newNoname {equality = false}))
				val l = Pat.var (r, Type.var(Tyvar.newNoname {equality = false}))
				val pat = Pat.tuple (Vector.new4 (i, j, k, l))				
			in				
				RFarrow (SOME pat, RFrecord([(f1, "1"), (f2, "2"), (f3, "3"), (f4, "4")], RelFrame.empty_refinement), f'') 
			end
		
		fun currydef2 f = 
			let val (x, y, z) = (Var.fromString (fresh_ident ()), Var.fromString (fresh_ident ()), Var.fromString (fresh_ident ()))
				val (f1, fy) = f x 
				val (f2, fz) = fy y
				val f'' = fz z
				val i = Pat.var (x, Type.var(Tyvar.newNoname {equality = false}))
				val j = Pat.var (y, Type.var(Tyvar.newNoname {equality = false}))
			in
				RFarrow (SOME i, f1, RFarrow (SOME j, f2, f''))				
			end
			
		fun currydef3 f = 
			let val (x, y, z, a) = (Var.fromString (fresh_ident ()), Var.fromString (fresh_ident ()), Var.fromString (fresh_ident ()), Var.fromString (fresh_ident ()))
				val (f1, fy) = f x 
				val (f2, fz) = fy y
				val (f3, fa) = fz z
				val f'' = fa a
				val i = Pat.var (x, Type.var(Tyvar.newNoname {equality = false}))
				val j = Pat.var (y, Type.var(Tyvar.newNoname {equality = false}))
				val k = Pat.var (z, Type.var(Tyvar.newNoname {equality = false}))
			in	
				RFarrow (SOME i, f1, RFarrow (SOME j, f2, RFarrow (SOME k, f3, f'')))			
			end
		
		fun defun f = (reset_idents (); def f)
		
		fun defun2 f = (reset_idents(); def2 f)
		
		fun defun3 f = (reset_idents(); def3 f)
		
		fun defun4 f = (reset_idents(); def4 f)
		
		fun currydefun2 f = (reset_idents(); currydef2 f)
		
		fun currydefun3 f = (reset_idents(); currydef3 f)
		
		fun doublerow x y = (x, y)
		
		fun triplerow x y = doublerow x y
		
    (* creates a frame var with empty refinement *)
		fun forall f = f (RelFrame.RFvar(Var.mk_ident "'a", RelFrame.empty_refinement)) 
		
		(*
    fun relop_frame qname lhs_rp rhs_rp1 rel_op rhs_rp2 =
		  (path, defun2 (fn x => triplerow uInt
		                (fn y => doublerow uInt
		                (fn z => (rInt qname z (equals (Predicate.PVar z) (Binop (Predicate.PVar x, opr, Predicate.PVar y))))))))
    *)

		val tag_function = "__tag"
		
		fun tag x = Predicate.FunApp(tag_function, [x])
		
		fun or_frame p1 p2 =
			(reset_idents ();	
		   	let val z = Var.fromString (fresh_ident ())
		   	in   
		   		rBool "||" z (riffo (tag (Predicate.PVar z)) (roro p1 p2))
	        end
	        )
		
		fun and_frame p1 p2 =
			(reset_idents ();
			let val z = Var.fromString (fresh_ident ())
			in
				rBool "&&" z (riffo (tag (Predicate.PVar z)) (rando p1 p2))
			end
			)
			
		fun equality_qualifier con exp =
			let 
        val x = Var.mk_ident "V" 
        val tyv = RP.make_typedvar(x)
				val rpred = RP.requals (RP.make_rrel (con,tyv)) exp
		   		val expstr = RP.pprint rpred 
		   	in (Var.mk_ident expstr, tyv, rpred) end

		fun not_frame p = 
			(reset_idents ();
			let val z  = Var.fromString (fresh_ident ())
			in
				rBool "not" z (riffo (tag (Predicate.PVar z)) (rnoto p))
			end
			)
		
		fun qbool_rel qname rel (z, r1, r2) = rBool qname z (riffo (tag (Predicate.PVar z)) (RPred ((RAtom (r1, rel, r2)))))
		
		(*
    fun poly_rel_frame path qname rel =
		  (path,
		   defun2 (forall (fn a => fn x => triplerow a
		   					(fn y => doublerow a 
		   						(fn z => qbool_rel qname rel (x, y, z))))))
    *)
		
		val mframes = [
		          
		]
	
		
		fun frames () =
			let 
				fun resolve_names x = List.map (x, (fn (id, fr) => (Var.fromString (List.first id), fr)))
			in
				resolve_names mframes
			end

		fun field_eq_qualifier name c rexp =
			let 
        val x = RP.make_typedvar (Var.mk_ident "x")
		  	in (Var.mk_ident "<field_eq>", x, (equals (Field (name, PVar x)) pexp)) end
		
		fun proj_eq_qualifier n pexp =
			let val x = Var.mk_ident "x" 
			in (Var.mk_ident "<tuple_nth_eq>", x, (equals (Proj (n, PVar x)) pexp)) end
	end
