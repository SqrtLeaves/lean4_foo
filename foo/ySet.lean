
class ySet (T: Type) where
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

def list_union {T: Type} (L: List (ySet T)) : ySet T := {
  is_element := fun (t : T) => ∃ s, s ∈ L ∧ t ∈ s
}

def union {T: Type} (S: ySet (ySet T)) : ySet T := {
  is_element := fun (t : T) => ∃ s, s ∈ S ∧ t ∈ s
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
