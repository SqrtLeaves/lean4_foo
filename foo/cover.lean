import foo.topology

structure Cover (Y X : TopoSpace) extends TopoMap Y X where
  cover_map_is_continuous : is_continuous = true


-- variable (is_connected_cover: ∀ (coverL Cover))

variable {Y X : TopoSpace}

variable {phi : TopoMap Y X}

-- variable {c: Cover phi}

def is_connected_cover (c : Cover Y X) : Prop :=
  c.source_space.is_connected = true

theorem check_is_connected_cover (c : Cover Y X) :
  is_connected_cover c <-> c.source_space.is_connected = true := by rfl





-- variable (is_connected_cover: Cover phi -> Prop)

-- variable (check_is_connected_cover: ∀ (cover: Cover phi), (is_connected_cover cover) <-> cover.cover_map.source_space.is_connected)
