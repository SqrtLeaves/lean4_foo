
structure TopoSpace where
  connected : Bool
  path_connected : Bool

structure TopoMap where
  source_space : TopoSpace
  target_space : TopoSpace
  continuous : Bool

structure Cover where
  cover_map : TopoMap
  cover_map_is_continuous : cover_map.continuous = true
  base_space : TopoSpace
  over_space : TopoSpace
