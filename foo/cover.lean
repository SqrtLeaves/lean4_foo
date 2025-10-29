import foo.topology

open NS_Topology

private def is_pairwise_disjoint (S: ySet (ySet T)) : Prop :=
  ∀ s0, ∀ s1, s0 ∈ S ∧ s1 ∈ S -> s0 ≠ s1 -> intersection [s0, s1] = emptyset

private def is_cover {Yc Xc: Type} {Y: TopoSpace Yc} {X: TopoSpace Xc} (s_map: TopoMap Y X) : Prop :=
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
        let res_map_on_U := TopoMap_restriction s_map U_as_subset
        ySetMap_img res_map_on_U.toySetMap = Nx ∧ is_embed_homeo.r res_map_on_U
      )
    )
  )

class Cover {Yc Xc: Type} {Y: TopoSpace Yc} {X: TopoSpace Xc}
  (s_map: TopoMap Y X) extends TopoMap Y X where
  map := s_map.map
  properly_covered : is_cover s_map


def trivial_cover {Xc: Type} (X: TopoSpace Xc) (_: I = DiscreteTopology S) :
  TopoMap (ProductTopology X I) X := {
    map :=
      fun xi => xi.1
  }

def is_connected_cover {f: TopoMap Y X} (_: Cover f) : Prop :=
  is_connected Y

def is_locally_trivially_covered (f: TopoMap Y X) : Prop := sorry

-- class is_cover_isomorphism (T: Type) where
--   r: T -> Prop

-- instance {p0: TopoMap Z X} {p1: TopoMap Y X}: is_cover_isomorphism  (
--   (Cover p0) × (Cover p1) × (TopoMap Z Y)
-- ) where
--     r C :=
--       let cover_map := C.2.2
--       let source_map := C.1
--       let target_map := C.2.1
--       is_homeo C.2.2 ∧ source_map.toTopoMap = (TopoMap_composition cover_map target_map.toTopoMap)

-- instance {p0: TopoMap Z X} {p1: TopoMap Y X}: is_cover_isomorphism  (
--   (Cover p0) × (Cover p1)
-- ) where
--     r C :=
--       let source_map := C.1
--       let target_map := C.2
--       ∃ (f: TopoMap Z Y), is_homeo f ∧ source_map.toTopoMap = (TopoMap_composition f target_map.toTopoMap)

def is_cover_isomorphism {p0: TopoMap Z X} {p1: TopoMap Y X}
  (source_map: Cover p0)  (target_map: Cover p1) (cover_map: TopoMap Z Y) : Prop :=
    is_homeo cover_map ∧ source_map.toTopoMap = (TopoMap_composition cover_map target_map.toTopoMap)


variable {Yc Xc: Type} {Y: TopoSpace Yc} {X: TopoSpace Xc} {f: TopoMap Y X} {c: Cover f}

theorem cover_is_surjective (map: Cover f) : is_surjective map.toySetMap := by sorry

theorem cover_is_locally_trivially_covered (f: TopoMap Y X) :
  is_locally_trivially_covered f <-> is_cover f := sorry


def fiber (c: Cover f) (x: Xc) : TopoSpace Yc := sorry

theorem connected_imp_homog (c : Cover f):
  is_connected X -> (
    ∃ T, ∃ S, ∃ (I: TopoSpace T) (_:I = DiscreteTopology S), (
      ∀ x, x ∈ X.base_set -> is_homeo (I, (fiber c x))
    )
  ) := sorry


-- A new theorem where you use the first one
theorem use_the_discrete_fiber (h_conn : is_connected X) (c : Cover f) :
  -- Let's prove something simple: the fiber over some point is homeomorphic to a discrete space
  ∃ (x : Xc) (_: x ∈ X.base_set), ∃ (I : TopoSpace _) (_: I = DiscreteTopology S), is_homeo (I, fiber c x) := by

  -- 1. Apply the theorem to get the proof of the existential statement
  let proof_of_exists := connected_imp_homog c h_conn

  -- 2. Use `obtain` to extract the objects and their proofs
  obtain ⟨T, S, I, h_I_is_discrete, h_fibers_are_homeo⟩ := proof_of_exists

  -- Now `I`, `h_I_is_discrete`, and `h_fibers_are_homeo` are in our context!

  -- 3. We can now finish our goal.
  -- Let's pick an arbitrary point `x₀` from the base set (assuming it's non-empty)
  let x₀ : Xc := sorry -- (proof that X.base_set is inhabited)

  -- Use the extracted proof `h_fibers_are_homeo` for our specific point x₀
  let homeo_at_x₀ := h_fibers_are_homeo x₀ (x₀.property)

  -- Now construct the proof for our goal
  exact ⟨x₀, I, sorry (* proof that I is discrete from h_I_is_discrete *), homeo_at_x₀⟩

-- theorem xx (f: TopoMap Y X) :
--   is_locally_trivially_covered f -> (
--     ∀ x, x ∈ X.base_set -> (
--       let px := f.reverse_map x
--       ∃ (NxT: TopoSpace Xc),
--       ∃ (NysT: TopoSpace Yc),
--       ∃ (p: TopoMap NysT NxT),
--       ∃ (I: TopoSpace Yc) (hI: I = DiscreteTopology px),
--       ∃ (g: TopoMap NysT (ProductTopology NxT I)),
--       let p_cover : Cover p := sorry
--       let t_cover : Cover (trivial_cover NxT hI) := sorry
--       X.is_open_neighbor NxT.base_set x ∧
--       is_cover p ∧
--       is_cover_isomorphism p_cover t_cover g
--     )
--   ) := sorry
