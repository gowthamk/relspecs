structure VarMap : ORD_MAP =
struct
  open Atoms
  structure VarKey (*: ORD_KEY*)= 
  struct
    type ord_key = Var.t
    fun compare (v1,v2) = 
      String.compare (Var.toString v1,Var.toString v2)
  end
  structure BM = BinaryMapFn(VarKey)
  open BM
end
