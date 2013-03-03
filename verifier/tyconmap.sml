signature TYCON_MAP =
sig
  include ATOMS
  type t
  type datatype_desc = {cons: {arg: CoreML.Type.t option,
                               con: Con.t} vector,
                        tycon: Tycon.t,
                        tyvars: Tyvar.t vector}
  val new_tycon_map : unit -> t
  val bind_datatypes : t -> datatype_desc vector -> unit
  val tycon_mem : t -> Tycon.t -> bool
  val cstr_mem : t -> Con.t -> bool
  val get_tyvars_by_cstr : t -> Con.t -> Tyvar.t list
  val get_argtys_by_cstr : t -> Con.t -> (Type_desc.type_desc*bool) list
  val get_tycon_def : t -> Tycon.t -> (Con.t * Type_desc.type_desc list) list
  val get_cstrs_by_tycon : t -> Tycon.t -> Con.t list
end
structure TyconMap : TYCON_MAP =
struct
  open HashTable
  open Atoms
  open Common
  open Type_desc

  type datatype_desc = {cons: {arg: CoreML.Type.t option,
                               con: Con.t} vector,
                        tycon: Tycon.t,
                        tyvars: Tyvar.t vector}

  type tycon_desc_map = (Tycon.t, (Con.t * Type_desc.type_desc list) list) hash_table

  type cstr_desc = {tyvars : (Tyvar.t list), 
      argtypes : (Type_desc.type_desc * bool) list}

  type cstr_desc_map = (Con.t,cstr_desc) hash_table

  type t = tycon_desc_map * cstr_desc_map 
 
  fun new_tycon_map () = 
    let
      val sdt = mkTable ((HashString.hashString) o (Tycon.toString), Tycon.equals) (37, Common.Not_found)
      val dt = mkTable ((HashString.hashString) o (Con.toString), Con.equals) (37, Common.Not_found)
    in
      (sdt,dt)
    end
 
 (* set of mutually recursive datatype definitions *)
  fun bind_datatypes (sdt,dt) v= Vector.foreach (v, 
    (fn {cons, tycon, tyvars} => 
      let
        val mydatatype = Tconstr (tycon, Vector.toListMap (tyvars,fn(v)=>(Tvar v)))
      in
        Vector.foreach (cons, (fn {arg, con} => 
          let 
            val tef_list = case arg of 
              NONE => []
            | SOME t => 
              let 
                val nt = CoreML.Type.toMyType t 
              in
                case (nt) of
                  Ttuple li => 
                    List.map (li, fn (Tfield (_, t')) => (t',Type_desc.sametype(t',mydatatype))
                                  | _ => (print "\nUnknow Type\n"; assertfalse ()))
                | _ => [(nt,Type_desc.sametype(nt,mydatatype))]
              end
            val te_list = List.map (tef_list, fn(x,y)=>x)
            val cstrdesc = {tyvars=(Vector.toList tyvars),argtypes=tef_list}
          in
            HashTable.insert dt (con, cstrdesc);
            if (HashTable.inDomain sdt tycon) then
              let val existings = HashTable.lookup sdt tycon
              in HashTable.insert sdt (tycon, (con, te_list) :: existings) end
            else
              HashTable.insert sdt (tycon, [(con, te_list)])
          end
           ))
                    
      end
    ))

  fun tycon_mem (sdt,dt) tycon = HashTable.inDomain sdt tycon

  fun cstr_mem (sdt,dt) con = HashTable.inDomain dt con

  fun get_tyvars_by_cstr (sdt,dt) con = 
    let
      val {tyvars,argtypes} = HashTable.lookup dt con
    in
      tyvars
    end

  fun get_argtys_by_cstr (sdt,dt) con=
    let
      val {tyvars,argtypes} = HashTable.lookup dt con
    in
      argtypes
    end

  fun get_tycon_def (sdt,dt) tyc = HashTable.lookup sdt tyc

  fun get_cstrs_by_tycon tm tycon = List.map(get_tycon_def tm tycon,fst)
end
