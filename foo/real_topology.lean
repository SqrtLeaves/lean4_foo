import foo.topology

def right_real_ray_closed (z: Rat) : ySet Rat := {
    is_element :=
        fun x => x >= z
}


def left_real_ray_closed (z: Rat) : ySet Rat := {
    is_element :=
        fun x => x <= z
}

def right_real_ray_open (z: Rat) : ySet Rat := {
    is_element :=
        fun x => x > z
}

def left_real_ray_open (z: Rat) : ySet Rat := {
    is_element :=
        fun x => x < z
}

def interval_open (z0 z1: Rat) : ySet Rat := {
    is_element :=
        fun x => z0 < x ∧ x < z1
}

def interval_closed (z0 z1: Rat) : ySet Rat := {
    is_element :=
        fun x => z0 <= x ∧ x <= z1
}

def real_topology_basis : ySet (ySet Rat) := {
    is_element :=
        fun I => ∃ (z0 z1: Rat), I = interval_open z0 z1
}

-- theorem _helper: yRat = union real_topology_basis := sorry

def real_topology : TopoSpace Rat := {
    base_set := yRat
    is_open := (
        fun U => ∃ F, F ⊆ real_topology_basis ∧ U = union F
    )

    base_is_open := by
        constructor

        case w => exact real_topology_basis
        case h =>
            constructor
            case left => apply is_self_subset
            case right =>
                -- simp [union]
                rw [<- set_equality0]
                constructor
                case left =>
                    intro x hx
                    have cj1: (interval_open (x-1) (x+1)) ∈ real_topology_basis := sorry
                    have cj2: x ∈ (interval_open (x-1) (x+1)) := sorry
                    have cj3: x ∈ union real_topology_basis := sorry
                    exact cj3
                case right =>
                    intro x hx
                    sorry

    empty_is_open := sorry
    opens_are_subsets_of_base := sorry
    open_union_is_open := sorry
    finite_open_intersection_is_open := sorry
}

theorem real_path_topology_helper (z0 z1: Rat): (interval_closed z0 z1) ⊆ yRat := sorry

def real_path_topology : TopoSpace Rat :=
    SubspaceTopology real_topology (interval_closed 0 1) (real_path_topology_helper 0 1)
