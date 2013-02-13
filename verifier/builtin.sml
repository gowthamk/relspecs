signature BUILTIN = 
	sig			
		include ATOMS
		
		val translated_name : (string, string) HashTable.hash_table
		
		val retranslated_name : (string, string) HashTable.hash_table
		
		val qsize_arr : Predicate.binrel -> Var.t -> Var.t -> Var.t -> Qualifier.t
		
		val qsize_str : Predicate.binrel -> Var.t -> Var.t -> Var.t -> Qualifier.t
		
		val mk_int : Qualifier.t list -> Frame.t
		val mk_string : Qualifier.t list -> Frame.t
		val mk_bool : Qualifier.t list -> Frame.t
		val mk_array : Frame.t -> Qualifier.t list -> Frame.t
		val mk_unit : unit -> Frame.t
		
		val uInt : Frame.t
		val uString : Frame.t
		val uBool : Frame.t
		val uUnit : Frame.t
		val uFloat : Frame.t
		val uChar :Frame.t
		
		val rInt : string -> Var.t -> Predicate.t -> Frame.t
		val rString : string -> Var.t -> Predicate.t -> Frame.t
		val rBool : string -> Var.t -> Predicate.t -> Frame.t
		val rArray : Frame.t -> string -> Var.t -> Predicate.t -> Frame.t
		
		
		val tag : Predicate.pexpr -> Predicate.pexpr
		
		val tag_function : string
		
		val frames : unit -> (Var.t * Frame.t) list

    val pprint_builtins : (Var.t * Frame.t) list -> unit
		
    val is_builtin : Var.t -> bool

		val equality_qualifier : Predicate.pexpr -> Qualifier.t

		val equality_refinement : Predicate.pexpr -> Frame.refinement

		val tag_refinement : int -> Frame.refinement
		
		val size_lit_refinement : int -> Frame.refinement
		
		val field_eq_qualifier : string -> Predicate.pexpr -> Qualifier.t
		
		val proj_eq_qualifier : int -> Predicate.pexpr -> Qualifier.t
		
		val and_frame : Predicate.t -> Predicate.t -> Frame.t 
		
		val or_frame : Predicate.t -> Predicate.t -> Frame.t
	end

structure Builtin (*: BUILTIN*) =
	struct
		open Atoms
		open Qualifier
		open Predicate
		open CoreML
		open Frame
		open Common
		open Smlsys
		
		(* For array length constraint, y == z in this case *)
		fun qsize funm rel x y z = (Var.mk_ident ("SIZE_" ^ (pprint_rel rel)), y,
		                       Atom(PVar z, rel, FunApp(funm, [PVar x])))
		
		fun qsize_arr rel x y z = qsize (HashTable.lookup translated_name "Array.length") rel x y z
		fun qsize_str rel x y z = qsize (HashTable.lookup translated_name "String.length") rel x y z
		
		fun qdim_row_arr rel x y z =  qsize ("nRows_0") rel x y z
		fun qdim_col_arr rel x y z =  qsize ("nCols_0") rel x y z
		
		fun qint rel i y =
		  (Var.mk_ident ("INT_" ^ (pprint_rel rel) ^ (Int.toString i)), y, Atom(PVar y, rel, PInt i))
		
		fun qrel rel x y =
		    (Var.mk_ident ("_" ^ (Var.toString x) ^ (pprint_rel rel) ^ (Var.toString y) ^ "_"), 
		     x,
		     Atom(PVar x, rel, PVar y))
		
		fun mk_int qs = Fconstr(Tycon.defaultInt (), [], ([], Qconst qs))
		fun mk_string qs = Fconstr(Tycon.vector, [(Fconstr(Tycon.defaultChar (), [], ([], Qconst [])))], ([], Qconst qs))
		fun mk_bool qs = Fconstr(Tycon.bool, [], ([], Qconst qs))
		fun mk_array f qs = Fconstr(Tycon.array, [f], ([], Qconst qs))
		fun mk_list f qs = Fconstr(Tycon.list, [f], ([], Qconst qs))
		fun mk_record fs qs = Frecord (fs, ([], Qconst qs))
		fun mk_unit () = Frecord ([], Frame.empty_refinement) (*Fconstr(Tycon.vector, [], ([], Qconst []))*)
		fun mk_ref f qs = Fconstr(Tycon.reff, [f], ([], Qconst qs))
		
		val uFloat = Fconstr(Tycon.defaultReal (), [], ([], Qconst []))
		val uChar = Fconstr(Tycon.defaultChar (), [], ([], Qconst []))
		val uString = mk_string []
		val uBool = mk_bool []
		val uInt = mk_int []
		val uUnit = mk_unit ()
		
		fun rString name v p = mk_string [(Var.mk_ident name, v, p)]
		fun rBool name v p = mk_bool [(Var.mk_ident name, v, p)]
		fun rInt name v p = mk_int [(Var.mk_ident name, v, p)]
		fun rArray b name v p = mk_array b [(Var.mk_ident name, v, p)]
		
		val char = ref 0
		
		fun reset_idents () = (char := ((Char.ord #"a") - 1))
		
		fun fresh_ident () = (incr char; Char.toString (Char.chr (!char)))
		
		fun def f =
			let val (x, y) = (Var.fromString (fresh_ident ()), Var.fromString (fresh_ident ()))
		  		val (f, fy) = f x
			in Farrow (SOME (Pat.var (x, Type.var(Tyvar.newNoname {equality = false}))), f, fy y) end
			
		fun def2 f = 
			let val (x, y, z) = (Var.fromString (fresh_ident ()), Var.fromString (fresh_ident ()), Var.fromString (fresh_ident ()))
				val (f1, fy) = f x 
				val (f2, fz) = fy y
				val f'' = fz z
				val i = Pat.var (x, Type.var(Tyvar.newNoname {equality = false}))
				val j = Pat.var (y, Type.var(Tyvar.newNoname {equality = false}))
				val pat = Pat.tuple (Vector.new2 (i, j))				
			in				
				Farrow (SOME pat, Frecord([(f1, "1"), (f2, "2")], Frame.empty_refinement), f'') 
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
				Farrow (SOME pat, Frecord([(f1, "1"), (f2, "2"), (f3, "3")], Frame.empty_refinement), f'') 
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
				Farrow (SOME pat, Frecord([(f1, "1"), (f2, "2"), (f3, "3"), (f4, "4")], Frame.empty_refinement), f'') 
			end
		
		fun currydef2 f = 
			let val (x, y, z) = (Var.fromString (fresh_ident ()), Var.fromString (fresh_ident ()), Var.fromString (fresh_ident ()))
				val (f1, fy) = f x 
				val (f2, fz) = fy y
				val f'' = fz z
				val i = Pat.var (x, Type.var(Tyvar.newNoname {equality = false}))
				val j = Pat.var (y, Type.var(Tyvar.newNoname {equality = false}))
			in
				Farrow (SOME i, f1, Farrow (SOME j, f2, f''))				
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
				Farrow (SOME i, f1, Farrow (SOME j, f2, Farrow (SOME k, f3, f'')))			
			end
		
		fun defun f = (reset_idents (); def f)
		
		fun defun2 f = (reset_idents(); def2 f)
		
		fun defun3 f = (reset_idents(); def3 f)
		
		fun defun4 f = (reset_idents(); def4 f)
		
		fun currydefun2 f = (reset_idents(); currydef2 f)
		
		fun currydefun3 f = (reset_idents(); currydef3 f)
		
		fun doublerow x y = (x, y)
		
		fun triplerow x y = doublerow x y
		
		fun forall f = f (Frame.Fvar(Var.mk_ident "'a", Frame.empty_refinement))
		
		fun op_frame path qname opr =
		  (path, defun2 (fn x => triplerow uInt
		                (fn y => doublerow uInt
		                (fn z => (rInt qname z (equals (PVar z) (Binop (PVar x, opr, PVar y))))))))
		
		
		val tag_function = "__tag"
		
		fun tag x = FunApp(tag_function, [x])
		
		fun or_frame p1 p2 =
			(reset_idents ();	
		   	let val z = Var.fromString (fresh_ident ())
		   	in   
		   		rBool "||" z (iffo (tag (PVar z)) (oro p1 p2))
	        end
	        )
		
		fun and_frame p1 p2 =
			(reset_idents ();
			let val z = Var.fromString (fresh_ident ())
			in
				rBool "&&" z (iffo (tag (PVar z)) (ando p1 p2))
			end
			)
			
		fun not_frame p = 
			(reset_idents ();
			let val z  = Var.fromString (fresh_ident ())
			in
				rBool "not" z (iffo (tag (PVar z)) (noto p))
			end
			)
		
		fun qbool_rel qname rel (x, y, z) = rBool qname z (iffo (tag (PVar z)) (Atom (PVar x, rel, PVar y)))
		
		fun poly_rel_frame path qname rel =
		  (path,
		   defun2 (forall (fn a => fn x => triplerow a
		   					(fn y => doublerow a 
		   						(fn z => qbool_rel qname rel (x, y, z))))))
		
		val mframes = [
		  op_frame ["+", "Pervasives"] "+" Plus,
		  op_frame ["-", "Pervasives"] "-" Minus,
		  op_frame ["/", "Pervasives"] "/" Div,
		  op_frame ["*", "Pervasives"] "*" Times,
		  
		  (["!_0", "Pervasives"],
		  defun (forall (fn a =>
		  			fn x => doublerow (mk_ref a []) 
		   			(fn _ => a)))
		  ),
		  
		  ([":=_0", "Pervasives"],
		   defun2 (forall (fn a =>
		          fn x => triplerow (mk_ref a [])
		          (fn y => doublerow a
		          (fn _ => uUnit)))) 
		  ),
		
		  (["lsl", "Pervasives"],
		   defun2 (fn x => triplerow uInt
		          (fn y => doublerow uInt
		          (fn z => rInt "lsr" z (le (PInt 0) (PVar z))
		               )))),
		   
		  (["lsr", "Pervasives"],
		   defun2 (fn x => triplerow uInt
		          (fn y => doublerow uInt
		          (fn z => rInt "lsr" z (le (PInt 0) (PVar z))
		               )))), 
		               
		  (["land", "Pervasives"],
		   defun2 (fn x => triplerow uInt
		          (fn y => doublerow uInt
		          (fn z => rInt "land" z
		              (imply (ando (ge (PVar x) (PInt 0)) (ge (PVar y) (PInt 0)))
		                 (big_and [le (PInt 0) (PVar z), le (PVar z) (PVar x), le (PVar z) (PVar y)])
		              )
		               )))), 
		
		  (["lor", "Pervasives"],
		   defun2 (fn x => triplerow uInt
		          (fn y => doublerow uInt
		          (fn z => rInt "lor" z
		              (imply (ando (ge (PVar x) (PInt 0)) (ge (PVar y) (PInt 0)))
		                 (big_and [le (PInt 0) (PVar z), ge (PVar z) (PVar x), ge (PVar z) (PVar y)])
		              )
		               )))),
		               
		  (["lxor", "Pervasives"],
		   defun2 (fn x => triplerow uInt
		          (fn y => doublerow uInt
		          (fn z => rInt "lxor" z
		              (True
		              )
		               )))),
		   
		  (["lnot", "Pervasives"],             
		  defun (fn x => doublerow uBool 
		   			(fn y => rInt "lnot" y True))),     
		  
		  (["mod", "Pervasives"],
		   defun2 (fn x => triplerow uInt
		          (fn y => doublerow uInt
		          (fn z => (rInt "mod" z
		            (equals (PVar z) (Binop (PVar x, Mod, PVar y)))
		            )
		            )))),
		            
		  (*
		  (ando
		            	(ando
		            		(ando 
		            			(imply (ge (PVar x) (PInt 0)) (le (PInt 0) (PVar z))) 
		            			(oro (l (PVar y) (PInt 0)) (g (PVar y) (PInt 0)))
		            		) 
		            		(imply (g (PVar y) (PInt 0)) (l (PVar z) (PVar y)))
		            	) 
		            	(equals (PVar z) (minuso (PVar x) (mulo (PVar y) (divo (PVar x) (PVar y)))))))
		  *)
		  
		  (["div", "Pervasives"],
		   defun2 (fn x => triplerow uInt
		          (fn y => doublerow uInt
		          (fn z =>
		            rInt "/" z
		               (equals (PVar z) (divo (PVar x) (PVar y))))))),
		
		  (*(["&&", "Pervasives"], and_frame ()),
		
		  (["||", "Pervasives"], or_frame ()), 
		
		  (["or", "Pervasives"], or_frame ()),
		
		  (["not", "Pervasives"],
		   defun (fn x => doublerow uBool 
		   			(fn y => rBool "NOT" y (iffo (tag (PVar y)) (equals (tag (PVar x)) (PInt 0)))))),*)
		
		  (*
		  (["ignore", "Pervasives"], defun (forall (fun a -> fun x -> a ==> fun y -> uUnit))),
		  *)
		  (*
		  (["succ", "Pervasives"], defun (fun x -> uInt ==> fun y -> rInt "succ" y ((PVar y) ==. ((PVar x) +- PInt 1)))),
		
		  (["pred", "Pervasives"], defun (fun x -> uInt ==> fun y -> rInt "pred" y ((PVar y) ==. ((PVar x) -- PInt 1)))),
		  *)
			
		  poly_rel_frame ["=_0", "Pervasives"] "=" Eq,
		  (* poly_rel_frame ["==", "Pervasives"] "==" Eq, *)
		  poly_rel_frame ["!=", "Pervasives"] "!=" Ne,
		  poly_rel_frame ["<>_0", "Pervasives"] "<>" Ne,
		  poly_rel_frame ["<", "Pervasives"] "<" Lt,
		  poly_rel_frame [">", "Pervasives"] ">" Gt,
		  poly_rel_frame [">=", "Pervasives"] ">=" Ge,
		  poly_rel_frame ["<=", "Pervasives"] "<=" Le,
		
		  (["length_0", "Array"],
		   defun (forall (fn a =>
		          fn x => doublerow (mk_array a [])
		          (fn y => mk_int [qsize_arr Eq x y y, qint Ge 0 y])))),
		
		  (["fromList_0", "Array"],
		   defun (forall (fn a =>
		          fn x => doublerow (mk_list a [])
		          (fn y => mk_array a [qsize_arr Eq x y y])))),
		
		  (["update_0", "Array"],
		   defun3 (forall (fn a =>
		          fn x => triplerow (mk_array a [])
		          (fn y => triplerow (mk_int [qsize_arr Lt x y y, qint Ge 0 y])
		          (fn _ => doublerow a
		          (fn _ => uUnit)))))),
		  
		  (["sub_0", "Array"],
		   defun2 (forall (fn a =>
		          fn x => triplerow (mk_array a [])
		          (fn y => doublerow (mk_int [qsize_arr Lt x y y, qint Ge 0 y])
		          (fn _ => a))))),
		
		  (["array_0", "Array"],
		   defun2 (forall (fn a =>
		          fn x => triplerow (rInt "NonNegSize" x (le (PInt 0) (PVar x)))
		          (fn y => doublerow a 
		          (fn z => mk_array a [qsize_arr Eq z z x]))))),
		
		  (["tabulate_0", "Array"],
		   defun2 (forall (fn a =>
		          fn x => triplerow (rInt "NonNegSize" x (le (PInt 0) (PVar x)))
		          (fn i => doublerow ((def (fn y => doublerow (rInt "Bounded" y (ando (le (PInt 0) (PVar y)) (l (PVar y) (PVar x)))) (fn _ => a))))
		          (fn z => mk_array a [qsize_arr Eq z z x]))))),
		  		
		  (["copy_0", "Array"],		          
		  defun (forall (fn a =>
		          fn x => doublerow ( mk_record [(mk_int [], "di"), (mk_array a [], "dst"), (mk_array a [], "src")] [
		          				(Var.mk_ident ("INT_" ^ (pprint_rel Ge) ^ (Int.toString 0)), x, Atom(Field ("di", (PVar x)), Ge, PInt 0)),
		          				(Var.mk_ident ("SIZE_" ^ (pprint_rel Le)), x,
		                       		Atom(Binop(Field ("di", PVar x), Plus, FunApp("length_0", [Field ("src", PVar x)])), Le, 
		                       			FunApp("length_0", [Field ("dst", PVar x)])))
		          			])
		          (fn _ => uUnit)))),        
		          
		  (["appi_0", "Array"],
		   currydefun2 (forall (fn a =>
		          fn x => triplerow ((def2 (fn y => triplerow (mk_int []) (fn j => doublerow a (fn _ => uUnit)))))
		          (fn i => doublerow (mk_array a [])
		          (fn _ => uUnit))))),
		          
		  (["foldl_0", "List"],
		  currydefun3 (forall (fn b => (forall (fn a =>
		          fn x => triplerow ((def2 (fn m => triplerow a (fn n => doublerow b (fn _ => b)))))
		          (fn y => triplerow b
		          (fn _ => doublerow (mk_list a [])
		          (fn _ => b)))))))),      
		  
		  (["app_0", "List"],
		   currydefun2 (forall (fn a =>
		          fn x => triplerow ((def (fn y => doublerow a (fn _ => uUnit))))
		          (fn i => doublerow (mk_list a [])
		          (fn _ => uUnit))))),
		  
		  
		  (["make_str", "String"],
		   defun2 (fn x => triplerow (rInt "NonNegSize" x (le (PInt 0) (PVar x)))
		          (fn c => doublerow uChar 
		          (fn s => mk_string [qsize_str Eq s s x])))),
		
		  (["size", "String"],
		   defun (fn x => doublerow (mk_string [])
		          (fn y => mk_int [qsize_str Eq x y y, qint Ge 0 y]))),
		
		  (["sub_1", "String"],
		   defun2 (forall (fn a =>
		          fn x => triplerow uString
		          (fn y => doublerow (mk_int [qsize_str Lt x y y, qint Ge 0 y])
		          (fn z => uChar))))),
		          
		  (["array_1", "Array2"],
		  defun3 (forall (fn a =>
		          fn x => triplerow (rInt "NonNegSize" x (le (PInt 0) (PVar x)))
		          (fn y => triplerow (rInt "NonNegSize" y (le (PInt 0) (PVar y)))
		          (fn _ => doublerow a
		          (fn z => mk_array a [qdim_row_arr Eq z z x, qdim_col_arr Eq z z y])))))),        
		  
		  (["sub_1", "Array2"],
		  defun3 (forall (fn a =>
		          fn x => triplerow (mk_array a [])
		          (fn i => triplerow (mk_int [qint Ge 0 i, qdim_row_arr Lt x i i])
		          (fn j => doublerow (mk_int [qint Ge 0 j, qdim_col_arr Lt x j j])
		          (fn _ => a)))))),
		  
		  (["update_1", "Arrat2"],
		  defun4 (forall (fn a =>
		  		  fn u => triplerow (mk_array a []) 
		          (fn i => triplerow (mk_int [qint Ge 0 i, qdim_row_arr Lt u i i])
		          (fn j => triplerow (mk_int [qint Ge 0 j, qdim_col_arr Lt u j j])
		          (fn _ => doublerow a
		          (fn _ => uUnit))))))),
		          
		  (["nRows_0", "Array2"], 
		  defun (forall (fn a =>
		          fn x => doublerow (mk_array a [])
		          (fn y => mk_int [qdim_row_arr Eq x y y, qint Ge 0 y])))),
		          
		  (["nCols_0", "Array2"],
		  defun (forall (fn a =>
		          fn x => doublerow (mk_array a [])
		          (fn y => mk_int [qdim_col_arr Eq x y y, qint Ge 0 y])))),
		          
		  (["sin", "Math"],         
		  defun (fn x => doublerow (uFloat)
		  		(fn y => uFloat
		  ))),
		  
		  (["cos", "Math"],
		  defun (fn x => doublerow (uFloat)
		  		(fn y => uFloat
		  ))), 
		  
		  (["real", "Real"],
		  defun (fn x => doublerow (uInt)
		  		(fn y => uFloat
		  ))),
		  		  
		  (["ignore_0", "Pervasives"],
		  defun (forall (fn a => 
		  		fn x => doublerow a 
		  		(fn y => uUnit
		  ))))
		  
		  (*
		  (["int", "Random"], defun (fun x -> rInt "PosMax" x (PInt 0 <. PVar x) ==>
		                             fun y -> rInt "RandBounds" y ((PInt 0 <=. PVar y) &&. (PVar y <. PVar x))))
		  *)
		]
	
		
		fun frames () =
			let 
				fun resolve_names x = List.map (x, (fn (id, fr) => (Var.fromString (List.first id), fr)))
			in
				resolve_names mframes
			end
		
    fun pprint_builtins (builtins : (Var.t * Frame.t) list) : unit=
      List.fold (
        builtins, 
        (),
        (fn ((var,frm),_) => (
          print ((Var.toString var)^" :: "^(Frame.pprint frm)^"\n")
        ))
      )

    fun is_builtin v = 
    let
      val bs = frames ()
    in
      List.exists (bs,(fn (v',_) => (Var.logic_equals (v,v')) orelse (Var.pointer_equals (v,v'))))
    end


		fun equality_qualifier exp =
			let val x = Var.mk_ident "V" 
				val pred = equals (PVar x) exp
		   		val expstr = Predicate.pprint pred 
		   	in (Var.mk_ident expstr, x, pred) end
		
		fun equality_refinement exp = ([], Qconst [equality_qualifier exp])
		
		fun tag_refinement t =
			let val x = Var.mk_ident "V"
		    	val pred = equals (tag (PVar x)) (PInt t)
		    	val expstr = Predicate.pprint pred 
		    in ([], Qconst [(Var.mk_ident expstr, x, pred)]) end
		
		fun size_lit_refinement i =
			let val x = Var.mk_ident "x"
			in
			    ([], Qconst [(Var.mk_ident "<size_lit_eq>",
			                  x,
			                  equals (FunApp(HashTable.lookup translated_name "Array.length", [PVar x])) (PInt i))])
			end
		
		fun field_eq_qualifier name pexp =
			let val x = Var.mk_ident "x" 
		  	in (Var.mk_ident "<field_eq>", x, (equals (Field (name, PVar x)) pexp)) end
		
		fun proj_eq_qualifier n pexp =
			let val x = Var.mk_ident "x" 
			in (Var.mk_ident "<tuple_nth_eq>", x, (equals (Proj (n, PVar x)) pexp)) end
	end
