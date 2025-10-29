-- #check (Type u)

-- inductive Traffic where
--   | tt: Nat -> Nat
--   | green

-- class tt where
--   a: Nat
--   fr : Nat -> tt := fun (x: Nat) => {a := x}

-- namespace tt
--   st


namespace ns0
def fooY (x: Nat) := x + 1


def f2 (x: Nat) := fooY x

end ns0


def f3 (x: Nat) := ns0.fooY x
