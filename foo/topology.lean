import foo.ySet

-- open _ySet

-- namespace _TopoSpace

  class TopoSpace (T: Type) where
    base_set : ySet T -- the underlying set

    is_open : ySet T -> Prop

    is_closed : ySet T -> Prop :=
      fun set => is_open (set_complement base_set set)

    base_is_open : is_open base_set
    empty_is_open : is_open ∅

    opens_are_subsets_of_base: ∀ s, is_open s -> s ⊆ base_set

    open_union_is_open :
      ∀ (S: ySet (ySet T)), ∀ s ∈ S, s ∈ (power_set base_set) ∧ is_open s -> is_open (union S)

    finite_open_intersection_is_open :
      ∀ (S: ySet (ySet T)), ∀ s ∈ S, s ∈ (power_set base_set) ∧ is_open s ∧ is_finite S ->
      is_open (intersection S)

  def is_open_cover (TS: TopoSpace T) (set: ySet T) (set_cover: ySet (ySet T)) : Prop :=
    ∀ s ∈ set_cover, TS.is_open s ->
    set ⊆ union set_cover

  def is_Hausdorff (TS: TopoSpace T) : Prop :=
    ∀ a0 ∈ TS.base_set, ∀ a1 ∈ TS.base_set, a0 ≠ a1 ->
    ∃ N0, ∃ N1, a0 ≠ a1 ∧ a0 ∈ N0 ∧ a1 ∈ N1 ∧ TS.is_open N0 ∧ TS.is_open N1 ∧
    (list_intersection [N0, N1] = ∅)

  def is_compact (TS: TopoSpace T) : Prop :=
    ∀ U, TS.is_open U -> ∀ C, is_open_cover TS U C ->
    ∃ C', C' ⊆ C ∧ is_finite C' ∧ is_open_cover TS U C'


  -- def is_compact (TS: TopoSpace) : Prop :=
  --   ∀ U, TS.is_open U →
  --     -- Create a local alias for the "is open cover of U" property.
  --     (let IsOpenCoverForU := fun Z => is_open_cover TS U Z) , IsOpenCoverForU C →

  --     ∃ C', C' ⊆ C ∧ is_finite C' ∧ IsOpenCoverForU C'

  def is_connected (TS: TopoSpace C) : Prop :=
    ∀ (A B: ySet C), TS.is_open A ∧ TS.is_open B ∧ A ≠ emptyset ∧ B ≠ emptyset ∧
    (list_union [A, B] = TS.base_set)
    -> list_intersection [A, B] ≠ emptyset

  def SubspaceTopology
    (TS: TopoSpace C) (sub_base_set : ySet C) (h : sub_base_set ⊆ TS.base_set) : TopoSpace C := {
    base_set := sub_base_set
    is_open := fun U => ∃ (N : ySet C), TS.is_open N ∧ U = list_intersection [N, sub_base_set]

    base_is_open := sorry
    empty_is_open := sorry
    finite_open_intersection_is_open := sorry
    open_union_is_open := sorry
    opens_are_subsets_of_base := sorry
  }


  class TopoMap {tS tT: Type} (source_space : TopoSpace tS) (target_space : TopoSpace tT)
    extends ySetMap source_space.base_set target_space.base_set

  -- def TopoMap_img {Bc: Type} {B: TopoSpace Bc} (f: TopoMap A B) : TopoSpace Bc  :=
  -- let a := 1
  -- {
  --   base_set := B.base_set
  -- }

  def TopoMap_composition (m0: TopoMap A B) (m1: TopoMap B C) : TopoMap A C := {
    map := fun a => m1.map (m0.map a)
  }

  def TopoMap_restriction {Ac Bc: Type} {A: TopoSpace Ac} {B: TopoSpace Bc}
    (f: TopoMap A B) (A': TopoSpace Ac)  (_: A'.base_set ⊆  A.base_set) : (TopoMap A' B) := {
    map := fun a => f.map a
  }

  def TopoMap_img_refine
    {Ac Bc: Type} {A: TopoSpace Ac} {B: TopoSpace Bc}
    (f: TopoMap A B) (B': TopoSpace Bc) (_: B'.base_set = ySetMap_img f.toySetMap)
    : (TopoMap A B') := {
    map := fun a => f.map a
  }

  def is_continuous {tS tT: Type} {S : TopoSpace tS} {T : TopoSpace tT} (map: TopoMap S T) : Prop :=
    ∀ NT, T.is_open NT -> S.is_open (map.reverse_map_set NT)

  def is_open_map (map: TopoMap S T) : Prop :=
    ∀ NS, S.is_open NS -> T.is_open (map.map_set NS)

  def is_homeo (map: TopoMap S T) : Prop :=
    is_continuous map ∧ is_open_map map ∧ is_bijective map.toySetMap

  def is_embed_homeo (map: TopoMap S T) : Prop :=
    is_continuous map ∧ is_injective map.toySetMap

-- end _TopoSpace
