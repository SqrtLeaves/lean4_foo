-- namespace _ySet

class ySet (T: Type) where
  -- carrier: Type u := T
  is_element: T -> Prop

instance {T : Type} : (Membership T) (ySet T) where
  mem s t := s.is_element t

instance {T : Type} : (Membership (ySet T)) (ySet (ySet T)) where
  mem s t := s.is_element t

def set_complement (set subset: ySet T) : ySet T :=
  {
    is_element := fun x => x ∈ set ∧ x ∉ subset
  }

def is_finite {T : Type} (s : ySet T) : Prop :=
  ∃ (n : Nat), ∃ (f : Fin n → T), ∀ (x : T), s.is_element x ↔ ∃ i, f i = x

def is_subset {T: Type} (subset set : ySet T) : Prop :=
  ∀ (t : T), t ∈ subset -> t ∈ set

def power_set {T: Type} (set: ySet T) : ySet (ySet T) := {
  is_element := fun (subset: ySet T) => is_subset subset set
}

def union {T: Type} (S: ySet (ySet T)) : ySet T := {
  is_element := fun (t : T) => ∃ s, s ∈ S ∧ t ∈ s
}

def list_union {T: Type} (L: List (ySet T)) : ySet T := {
  is_element := fun (t : T) => ∃ s, s ∈ L ∧ t ∈ s
}

def disjoint_union {T: Type} (S: ySet (ySet T)) : ySet ((ySet T) × T) := {
  is_element := fun p =>
    let (s, t) := p
    s ∈ S ∧ t ∈ s
}
def intersection {T: Type} (S: ySet (ySet T)) : ySet T := {
  is_element := fun (t : T) => (∀ s, s ∈ S -> t ∈ s)
}

def list_intersection {T: Type} (L: List (ySet T)) : ySet T := {
  is_element := fun (t : T) => (∀ s, s ∈ L -> t ∈ s)
}

def emptyset {T: Type} : ySet T := {
  is_element := fun (t: T) => False
}

notation lhs:65 " ⊆ " rhs:65 => is_subset lhs rhs
notation lhs:65 " ⊇ " rhs:65 => is_subset rhs lhs
notation " ∅ " => emptyset

axiom emptyset_is_subset {T: Type}
  (base_s: ySet T): emptyset ⊆ base_s

theorem subset_union_closed {T: Type}
  (base_s: ySet T)
  (S: ySet (ySet T))
  (h: ∀ s, S.is_element s -> s ⊆ base_s):
  is_subset (union S) base_s := sorry

theorem subset_intersection_closed {T: Type}
  (base_s: ySet T)
  (S: ySet (ySet T))
  (h: ∀ s, s ∈ S -> s ⊆ base_s):
  is_subset (intersection S) base_s := sorry

theorem subset_transfer {T: Type}
  (s0 s1 s2: ySet T) (h01: s0 ⊆ s1) (h12: s1 ⊆ s2) :
  is_subset s0 s2 := sorry

theorem union_complement
  (set: ySet T)
  (subset_collection: ySet (ySet T)) :
  let subset_c_collection : ySet (ySet T) := {
    is_element := fun x => set_complement set x ∈ subset_collection
  }
  set_complement set (union subset_collection) = intersection subset_c_collection :=
  sorry

theorem intersection_complement
  (set: ySet T)
  (subset_collection: ySet (ySet T)) :
  let subset_c_collection : ySet (ySet T) := {
    is_element := fun x => set_complement set x ∈ subset_collection
  }
  set_complement set (intersection subset_collection) = union subset_c_collection :=
  sorry

theorem is_self_subset (set: ySet T) : is_subset set set := sorry



class ySetMap {sT tT: Type} (source_set: ySet sT) (target_set: ySet tT) where
  map : sT -> tT
  reverse_map : tT -> ySet sT :=
    fun y => {
      is_element := fun x => map x = y
    }

  map_set : ySet sT -> ySet tT :=
    fun S => {
      is_element :=
        fun y => ∃ x ∈ S, map x = y
    }
  reverse_map_set : ySet tT -> ySet sT :=
    fun S => {
      is_element :=
        fun x => (map x) ∈ S
    }


def is_injective (map: ySetMap S T) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, map.map a = map.map b -> a = b

def is_surjective (map: ySetMap S T) : Prop :=
  ∀ a, a ∈ T -> ∃ s, s ∈ S ∧ map.map s = a

def is_bijective (map: ySetMap S T) : Prop :=
  is_injective map ∧ is_surjective map

theorem set_equality0 (S0 S1: ySet T) :
  ((∀ x0, x0 ∈ S0 -> x0 ∈ S1) ∧ (∀ x1, x1 ∈ S1 -> x1 ∈ S0)) <-> S0 = S1 :=
  sorry

def yRat: ySet Rat := {
  is_element :=
    fun _ => true
}

-- end _ySet

-- macro lhs:term:65 " ⊗ " rhs:term:65 : term =>
--   -- This is the rewrite rule.
--   -- It builds the syntax for a new `ySet` object.
--   `({ is_element := fun t => ($lhs).is_element t ∧ ($rhs).is_element t })

-- variable {s0 s1 s2: ySet T}

-- example : s0 ⊆ (list_union [s0, s1]) := by
--   simp [is_subset]
--   intro t h_t_in_s0
--   simp [list_union]
--   left
--   trivial
