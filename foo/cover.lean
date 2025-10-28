import foo.topology

private def is_disjoint_set_collection (S: ySet (ySet T)) : Prop :=
  ∀ s0, s0 ∈ S -> ∀ s1, s1 ∈ S ∧ s0 ≠ s1 -> list_intersection [s0, s1] = emptyset

def is_cover {Yc Xc: Type} {Y: TopoSpace Yc} {X: TopoSpace Xc} (map :TopoMap Y X) : Prop :=
  ∀ x, x ∈ X.base_set -> ∃ Nx, x ∈ Nx ∧ X.is_open Nx ->
  ∃ (open_stacks: ySet (ySet Yc)), map.reverse_map_set Nx = union open_stacks ->
  ∀ U (hU: U ∈ open_stacks ∧ Y.is_open U),
  let U_as_subset: U ⊆ Y.base_set := Y.opens_are_subsets_of_base U hU.2
  let U_as_subspace := SubspaceTopology Y U U_as_subset
  let res_map_on_U := TopoMap_restriction map U_as_subspace U_as_subset;
  is_homeo res_map_on_U

def is_connected_cover (map: TopoMap Y X) : Prop :=
  is_cover map ∧ is_connected Y

def is_cover_morphism
  (source_map: TopoMap Z X)
  (target_map: TopoMap Y X)
  (_: is_cover source_map)
  (_: is_cover target_map)
  (cover_map: TopoMap Z Y) : Prop :=
  is_continuous cover_map ∧ source_map = (TopoMap_composition cover_map target_map)


-- theorem cover_is_surjective (map: TopoMap Y X) (h0: is_cover Y X map) : is_surjective map.toySetMap := by sorry

-- theorem cover_is_surjective (map: TopoMap Y X) (h0: is_cover Y X map) : is_surjective map.toySetMap := by
--   -- Goal: ∀ a, a ∈ X.base_set → ∃ b, b ∈ Y.base_set ∧ map.toySetMap b = a
--   simp [is_surjective]
--   intro a a_in_X

--   -- Unpack the is_cover hypothesis for our specific point 'a'
--   rcases h0 a a_in_X with ⟨Nx, ⟨a_in_Nx, hNx_open⟩, open_stacks, h_union, h_all_U_props⟩

--   -- We need to know that the preimage of Nx is non-empty. A standard covering
--   -- space definition implies the stacks U are non-empty. Let's assume this and pick one.
--   -- This is a critical step that might require an axiom from your definition of is_cover.
--   have h_nonempty : (open_stacks : Set (Set Yc)).Nonempty := by
--     -- This part needs a formal proof, likely from an axiom that fibers are non-empty.
--     -- If open_stacks were empty, its union would be empty, meaning the preimage of a
--     -- neighborhood of 'a' is empty, which shouldn't happen in a cover.
--     sorry -- Assuming this can be proven from a more complete definition.

--   -- Get a specific stack 'U' from the collection of open_stacks
--   rcases h_nonempty with ⟨U, hU_mem⟩

--   -- Now we have a specific stack U. Let's get its properties.
--   -- We need to know U is open to apply h_all_U_props. This should be a property
--   -- of the stacks. Let's assume your 'is_open' property is part of the contract.
--   have hU_open : Y.is_open U := by
--     -- This proof would come from the properties of open_stacks
--     sorry

--   -- Apply the property for our specific stack U
--   let h_U_prop := h_all_U_props U ⟨hU_mem, hU_open⟩

--   -- 'h_U_prop' is a proof of 'is_homeo ...'. A homeomorphism is surjective.
--   -- Let's assume is_homeo implies is_surjective for the restricted map.
--   have h_restr_surj : is_surjective (TopoMap_restriction map U Nx).toySetMap := by
--     -- This proof follows from the definition of is_homeo
--     simp [is_homeo] at h_U_prop
--     sorry -- Assuming is_homeo implies bijective, which implies surjective

--   -- Unfold the surjectivity of the restricted map
--   simp [is_surjective] at h_restr_surj
--   -- Now h_restr_surj : ∀ (x : Xc), x ∈ Nx → ∃ (y : Yc), y ∈ U ∧ map.toySetMap y = x

--   -- We know a ∈ Nx, so we can apply this to find our point 'b'
--   rcases h_restr_surj a a_in_Nx with ⟨b, b_in_U, h_map_eq_a⟩

--   -- We found our candidate 'b'. Now we must prove it satisfies the goal.
--   -- Goal: ∃ b, b ∈ Y.base_set ∧ map.toySetMap b = a
--   exists b

--   -- We need to prove two things: b ∈ Y.base_set and map.toySetMap b = a
--   -- We already have the second one: h_map_eq_a
--   -- For the first, we know b ∈ U and U must be a subset of Y.base_set
--   have hU_subset : U ⊆ Y.base_set := Y.opens_are_subsets_of_base U hU_open
--   let b_in_base_set := hU_subset b_in_U

--   -- Now we have both proofs
--   exact ⟨b_in_base_set, h_map_eq_a⟩
