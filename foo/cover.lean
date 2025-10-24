import Mathlib.Data.Set.Basic -- Import the library for Set notation

structure TopoSpace where
  carrier : Type u
  is_connected : Bool
  is_path_connected : Bool

structure TopoElement (ts: TopoSpace) where
  topo_space := ts

structure TopoMap (source_ target_: TopoSpace) where
  is_continuous : Bool
  source_space := source_
  target_space := target_
  apply : source_space.carrier -> target_space.carrier
  reverse_apply : target_space.carrier -> Set source_space.carrier

structure Cover {Y X: TopoSpace} (map: TopoMap Y X) where
  cover_map := map
  cover_map_is_continuous : cover_map.is_continuous = true

-- variable (is_connected_cover: ∀ (coverL Cover))

variable {Y X: TopoSpace}

variable {phi: TopoMap Y X}

-- variable {c: Cover phi}

def is_connected_cover (c: Cover phi) : Prop :=
  c.cover_map.source_space.is_connected = true

theorem check_is_connected_cover (c: Cover phi) : is_connected_cover c <-> c.cover_map.source_space.is_connected = true := by rfl





-- variable (is_connected_cover: Cover phi -> Prop)

-- variable (check_is_connected_cover: ∀ (cover: Cover phi), (is_connected_cover cover) <-> cover.cover_map.source_space.is_connected)
