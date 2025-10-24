-- import «foo».Basic

-- 1. Define the mathematical "class" M as a structure.
-- It has two properties, Ma and Mb, which are booleans (true/false).
structure M where
  Ma : Bool
  Mb : Bool

-- 2. Define the statement S and the theorem T.
-- We declare S as an abstract function from M to a proposition (Prop).
variable (S : M → Prop)

-- We state your theorem T as a hypothesis `hT`.
-- It says that for any `m`, `S m` is true if and only if
-- `m.Ma` is true AND `m.Mb` is false.
variable (hT : ∀ (m : M), S m ↔ (m.Ma = true ∧ m.Mb = false))

-- 3. The proof demo.
-- We create an example (which is like a mini-theorem) to prove the goal.
example (m : M) (h_ma_true : m.Ma = true) (h_mb_true : m.Mb = true) : (S m → False) := by
  -- The goal is to prove `¬ (S m)`, which is shorthand for `S m → False`.
  -- We start by assuming `S m` is true and show it leads to a contradiction.
  intro hS

  -- We have the general theorem `hT` which works for all `m`.
  -- Let's apply it to our specific `m`.
  specialize hT m

  -- `hT` is now `S m ↔ (m.Ma = true ∧ m.Mb = false)`.
  -- Since we assumed `hS : S m`, we can use the theorem to deduce the right side.
  -- The `.mp` stands for "modus ponens" and gets the forward implication (`→`).
  have h_and : m.Ma = true ∧ m.Mb = false := (hT).mp hS

  -- From the "and" statement, we can extract the second part.
  have h_mb_false : m.Mb = false := h_and.right

  -- Now we have a contradiction!
  -- We were given `h_mb_true : m.Mb = true` from the start.
  -- We just proved `h_mb_false : m.Mb = false`.
  -- Let's show this to Lean. We can rewrite `m.Mb` in `h_mb_true` using our new finding.
  rw [h_mb_false] at h_mb_true

  -- After the rewrite, `h_mb_true` becomes `false = true`, which is a known contradiction.
  -- The `contradiction` tactic finds this and closes the goal.
  contradiction
