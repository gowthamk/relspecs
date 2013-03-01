signature INT_MAP =
sig
  include ORD_MAP where type Key.ord_key = Int.int
  val find_crash : 'a map * Int.int -> 'a
end
structure IntMap : INT_MAP =
struct
  exception Not_found
  open IntBinaryMap
  fun find_crash (m,k) = case find (m,k) of
      SOME p => p
    | NONE => raise Not_found
end
