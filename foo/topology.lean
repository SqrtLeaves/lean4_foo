import foo.ySet

class TopoSpace where
  carrier : Type
  base_set : ySet carrier -- the underlying set
  open_set_collection : ySet (ySet carrier)

  is_open : ySet carrier -> Prop :=
    fun set => set ∈ open_set_collection

  is_closed : ySet carrier -> Prop :=
    fun set => is_open (set_complement base_set set)

  base_is_open : is_open base_set
  empty_is_open : is_open ∅

  opens_are_subsets_of_base:
    ∀ s ∈ open_set_collection, s ⊆ base_set

  open_union_is_open :
    ∀ (S: ySet (ySet carrier)), ∀ s ∈ S, s ∈ (power_set base_set) ∧ is_open s -> is_open (union S)

  finite_open_intersection_is_open :
    ∀ (S: ySet (ySet carrier)), ∀ s ∈ S, s ∈ (power_set base_set) ∧ is_open s ∧ is_finite S ->
    is_open (intersection S)

def is_open_cover (TS: TopoSpace) (set: ySet TS.carrier) (set_cover: ySet (ySet TS.carrier)) : Prop :=
  ∀ s ∈ set_cover, TS.is_open s ->
  set ⊆ union set_cover

def is_Hausdorff (TS: TopoSpace) : Prop :=
  ∀ a0 ∈ TS.base_set, ∀ a1 ∈ TS.base_set, a0 ≠ a1 ->
  ∃ N0, ∃ N1, a0 ≠ a1 ∧ a0 ∈ N0 ∧ a1 ∈ N1 ∧ TS.is_open N0 ∧ TS.is_open N1 ∧
  (list_intersection [N0, N1] = ∅)

def is_compact (TS: TopoSpace) : Prop :=
  ∀ U, TS.is_open U -> ∀ C, is_open_cover TS U C ->
  ∃ C', C' ⊆ C ∧ is_finite C' ∧ is_open_cover TS U C'


-- def is_compact (TS: TopoSpace) : Prop :=
--   ∀ U, TS.is_open U →
--     -- Create a local alias for the "is open cover of U" property.
--     (let IsOpenCoverForU := fun Z => is_open_cover TS U Z) , IsOpenCoverForU C →

--     ∃ C', C' ⊆ C ∧ is_finite C' ∧ IsOpenCoverForU C'

def is_connected (TS: TopoSpace) : Prop :=
  ∀ (A B: ySet TS.carrier), TS.is_open A ∧ TS.is_open B ∧ A ≠ emptyset ∧ B ≠ emptyset ∧
   (list_union [A, B] = TS.base_set)
  -> list_intersection [A, B] ≠ emptyset

def is_path_connected (TS: TopoSpace) : Prop := sorry


class TopoMap (source_space target_space : TopoSpace) where
  map : source_space.carrier -> target_space.carrier
  reverse_map : target_space.carrier -> ySet source_space.carrier :=
    fun y => {
      is_element := fun x => map x = y
    }

  map_set : ySet source_space.carrier -> ySet target_space.carrier :=
    fun S => {
      is_element :=
        fun y => ∃ x ∈ S, map x = y
    }
  reverse_map_set : ySet target_space.carrier -> ySet source_space.carrier :=
    fun S => {
      is_element :=
        fun x => (map x) ∈ S
    }


def is_continuous {S T: TopoSpace} (map: TopoMap S T) : Prop :=
  ∀ (NT: ySet T.carrier), T.is_open NT -> S.is_open (map.reverse_map_set NT)

def is_injective (map: TopoMap S T) : Prop :=
  ∀ a ∈ S.base_set, ∀ b ∈ S.base_set, map.map a = map.map b -> a = b

def is_surjective (map: TopoMap S T) : Prop :=
  ∀ a, a ∈ T.base_set -> ∃ s, s ∈ S.base_set ∧ map.map s = a

def is_bijective (map: TopoMap S T) : Prop :=
  is_injective map ∧ is_surjective map

def is_homeo (map: TopoMap S T) : Prop :=
  is_continuous map ∧ is_bijective map
