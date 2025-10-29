import foo.topology

open NS_Topology

private def is_pairwise_disjoint (S: ySet (ySet T)) : Prop :=
  ∀ s0, ∀ s1, s0 ∈ S ∧ s1 ∈ S -> s0 ≠ s1 -> intersection [s0, s1] = emptyset

class Cover {Yc Xc: Type} {Y: TopoSpace Yc} {X: TopoSpace Xc}
  (s_map: TopoMap Y X) extends TopoMap Y X where
  map := s_map.map
  properly_covered :
    ∀ x, x ∈ X.base_set -> ∃ Nx, x ∈ Nx ∧ X.is_open Nx ∧
  (
    ∃ (open_stacks: ySet (ySet Yc)),
    s_map.reverse_map_set Nx = union open_stacks ∧
    is_pairwise_disjoint open_stacks ∧
    (
      ∀ U ∈ open_stacks, Y.is_open U ∧
      (
        let U_as_subset: U ⊆ Y.base_set := Y.opens_are_subsets_of_base U sorry
        let U_as_subspace := SubspaceTopology Y U U_as_subset
        let res_map_on_U := TopoMap_restriction s_map U_as_subspace U_as_subset
        ySetMap_img res_map_on_U.toySetMap = Nx ∧ is_embed_homeo.r res_map_on_U
      )
    )
  )

-- def is_cover {Yc Xc: Type} {Y: TopoSpace Yc} {X: TopoSpace Xc} (map :TopoMap Y X) : Prop :=
--   ∀ x, x ∈ X.base_set -> ∃ Nx, x ∈ Nx ∧ X.is_open Nx ∧
--   (
--     ∃ (open_stacks: ySet (ySet Yc)),
--     map.reverse_map_set Nx = union open_stacks ∧
--     is_pairwise_disjoint open_stacks ∧
--     (
--       ∀ U ∈ open_stacks, Y.is_open U ∧
--       (
--         let U_as_subset: U ⊆ Y.base_set := Y.opens_are_subsets_of_base U sorry
--         let U_as_subspace := SubspaceTopology Y U U_as_subset
--         let res_map_on_U := TopoMap_restriction map U_as_subspace U_as_subset
--         ySetMap_img res_map_on_U.toySetMap = Nx ∧ is_embed_homeo.r res_map_on_U
--       )
--     )
--   )

def trivial_cover {Xc: Type} (X: TopoSpace Xc) (_: I = DiscreteTopology S) :
  TopoMap (ProductTopology X I) X := {
    map :=
      fun xi => xi.1
  }

def is_connected_cover {f: TopoMap Y X} (_: Cover f) : Prop :=
  is_connected Y

class is_cover_isomorphism (T: Type) where
  r: T -> Prop

instance {p0: TopoMap Z X} {p1: TopoMap Y X}: is_cover_isomorphism  (
  (Cover p0) × (Cover p1) × (TopoMap Z Y)
) where
    r C :=
      let cover_map := C.2.2
      let source_map := C.1
      let target_map := C.2.1
      is_homeo C.2.2 ∧ source_map.toTopoMap = (TopoMap_composition cover_map target_map.toTopoMap)

instance {p0: TopoMap Z X} {p1: TopoMap Y X}: is_cover_isomorphism  (
  (Cover p0) × (Cover p1)
) where
    r C :=
      let source_map := C.1
      let target_map := C.2
      ∃ (f: TopoMap Z Y), is_homeo f ∧ source_map.toTopoMap = (TopoMap_composition f target_map.toTopoMap)

theorem cover_is_surjective (map: Cover f) : is_surjective map.toySetMap := by sorry
