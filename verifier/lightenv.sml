

signature LIGHTENV = 
	sig
		include ATOMS
		
		type t = (Var.t, Frame.t) HashTable.hash_table
		
		val empty : int -> t
		val mem : Var.t -> t -> bool
		val find : Var.t -> t -> Frame.t
		val fold : (Var.t -> Frame.t -> 'a -> 'a) -> t -> 'a -> 'a
		val add : Var.t -> Frame.t -> t -> t
		val update : Var.t -> Frame.t -> t -> unit
		val copy : t -> t
		val iter : (Var.t -> Frame.t -> unit) -> t -> unit
		val maplist : (Var.t -> Frame.t -> 'a) -> t -> 'a list
		val maplistfilter : (Var.t -> Frame.t -> 'a option) -> t -> 'a list
		val filterlist : (Var.t -> Frame.t -> bool) -> t -> Frame.t list
		val mapfilter : (Var.t -> Frame.t -> 'a option) -> t -> 'a list
		val addn : (Var.t * Frame.t) list -> t -> t
		val cardinality : t -> int
		val compare : t -> t -> int
		val domain : t -> Var.t list
		
		val env_bind: t -> CoreML.Pat.t -> Frame.t -> t
		val new_env_bind: t -> CoreML.Pat.t -> Frame.t -> TyconMap.t -> t
		val env_bind_record : t -> CoreML.Pat.t -> Frame.t -> Var.t -> t
		val pprint_fenv: t -> string
		val pprint_fenv_except: (t*(Var.t -> bool)) -> string
    val pprint_guard : (Var.t * int * bool) list -> string
	end


structure Lightenv : LIGHTENV = 
	struct 
		open Atoms
		open HashTable
		open Common
		
		type t = (Var.t, Frame.t) hash_table
				
		fun empty initial_size = 
			HashTable.mkTable (HashString.hashString o (Var.toString), Var.logic_equals) (initial_size, Not_found)
			
		fun mem x m = case (HashTable.find m x) of SOME _ => true | NONE => false
		
		fun find x m = case (HashTable.find m x) of SOME v => v | NONE => raise Not_found
		
		fun fold f m c = HashTable.foldi (fn(k,v,c') => f k v c') c m 
		
		fun add x b m =  (let val m' = HashTable.copy m in HashTable.insert m' (x, b); m' end)
		
		fun copy m = HashTable.copy m
		
		fun update x b m = HashTable.insert m (x, b)
		
		(* its type is (key -> 'a -> unit) -> 'a t -> unit *)
		fun iter f s = List.foreach((HashTable.listItemsi s), (fn(key, v) => f key v))
		
		fun maplist f env =
		  fold (fn k => fn v =>fn r => (f k v)::r) env []
		
		fun maplistfilter f env =
		  fold (fn k => fn v => fn r => let val c = f k v in case c of SOME c => c::r | NONE => r end) env []
		
		fun filterlist f env =
		  fold (fn k => fn v => fn r => if f k v then v::r else r) env []
		
		fun mapfilter f env =
		  fold (fn k => fn v => fn r => case f k v of SOME x => x::r | NONE => r) env []
		
		fun addn items env = 
			let val env' = HashTable.copy env
			in
				List.foreach (items, fn (k,v) => (HashTable.insert env' (k, v))); env'
			end
		
		fun cardinality e = fold (fn _ => fn _ => fn c => c + 1) e 0
		
		fun compare e1 e2 = 
			let	val n1 = (cardinality e1) 
				val n2 = (cardinality e2)
			in if (n1 < n2) then ~1
				else if (n1 = n2) then 0
				else 1
			end
		
		fun domain env = maplist (fn k => fn _ => k) env
		
    val spc = "                           "

		fun pprint_fenv fenv = fold (fn k => fn v => fn c => (c^spc^(Frame.unique_name k)^"="^(Frame.pprint v)^"\n")) fenv ""

		fun pprint_fenv_except (fenv,test) = fold (fn k => fn v => fn c => (if (not (test k))
      then (c^spc^(Frame.unique_name k)^"="^(Frame.pprint v)^"\n")
      else c )) fenv ""

    fun pprint_guard guard = List.fold(guard,"",
      (fn ((gv,i,b),s) => s^spc^(Var.toString gv)^"=("^(Int.toString i)^","^(Bool.toString b)^")"))
		
		fun env_bind env pat frame = addn (Frame.bind pat frame) env

		fun new_env_bind env pat frame tm = addn (Frame.new_bind pat frame tm) env
		
		fun env_bind_record env pat frame record_var = addn (Frame.bind_record pat frame record_var) env
	end
