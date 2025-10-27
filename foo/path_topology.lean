import foo.topology
import foo.real_topology
open _ySet
-- open _TopoMap
namespace _TopoSpace

def is_path {TS: TopoSpace T} (path: TopoMap real_path_topology TS) := is_continuous path

def is_path_connected (TS: TopoSpace C) : Prop :=
  ∀ a, a ∈ TS.base_set -> ∀ b, b ∈ TS.base_set ->
  ∃ (p: TopoMap real_path_topology TS), is_path p ∧ (p.map 0) = a ∧ (p.map 1) = b

theorem path_connected_imp_connected : ∀ (TS: TopoSpace C),
  is_path_connected TS -> is_connected TS := sorry

end _TopoSpace
