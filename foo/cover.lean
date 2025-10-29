import foo.topology

open NS_Topology

private def is_pairwise_disjoint (S: ySet (ySet T)) : Prop :=
  ∀ s0, ∀ s1, s0 ∈ S ∧ s1 ∈ S ∧ s0 ≠ s1 -> intersection [s0, s1] = emptyset

def is_cover {Yc Xc: Type} {Y: TopoSpace Yc} {X: TopoSpace Xc} (map :TopoMap Y X) : Prop :=
  ∀ x, x ∈ X.base_set -> ∃ Nx, x ∈ Nx ∧ X.is_open Nx ∧
  (
    ∃ (open_stacks: ySet (ySet Yc)),
    map.reverse_map_set Nx = union open_stacks ∧
    is_pairwise_disjoint open_stacks ∧
    (
      ∀ U ∈ open_stacks, Y.is_open U ∧
      (
        let U_as_subset: U ⊆ Y.base_set := Y.opens_are_subsets_of_base U sorry
        let U_as_subspace := SubspaceTopology Y U U_as_subset
        let res_map_on_U := TopoMap_restriction map U_as_subspace U_as_subset
        ySetMap_img res_map_on_U.toySetMap = Nx ∧ is_embed_homeo.r res_map_on_U
      )
    )
  )

def trivial_cover {Xc: Type} (X: TopoSpace Xc) (_: I = DiscreteTopology S) :
  TopoMap (ProductTopology X I) X := {
    map :=
      fun xi => xi.1
  }

def is_connected_cover (map: TopoMap Y X) : Prop :=
  is_cover map ∧ is_connected Y

def is_cover_morphism
  (source_map: TopoMap Z X)
  (target_map: TopoMap Y X)
  (_: is_cover source_map)
  (_: is_cover target_map)
  (cover_map: TopoMap Z Y) : Prop :=
  is_continuous cover_map ∧ source_map = (TopoMap_composition cover_map target_map)

-- def is_cover_isomorphism
--   (source_map: TopoMap Z X)
--   (target_map: TopoMap Y X)
--   (_: is_cover source_map)
--   (_: is_cover target_map)
--   (cover_map: TopoMap Z Y) : Prop :=
--   is_homeo cover_map ∧ source_map = (TopoMap_composition cover_map target_map)

class is_cover_isomorphism (T: Type) where
  r: T -> Prop

-- instance: is_cover_isomorphism (
--   (TopoMap Z X) × (TopoMap Y X) × Prop × Prop
-- ) where
--     r L := true

theorem cover_is_surjective (map: TopoMap Y X) (h0: is_cover map) : is_surjective map.toySetMap := by sorry
