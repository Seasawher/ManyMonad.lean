import ManyMonad.Basic

variable {α β : Type}

/-- Many は Functor 則を満たす -/
instance : LawfulFunctor Many where
  map_const := by
    intro α β
    rfl
  id_map := by
    intro α x
    dsimp [Functor.map]
    induction x with
    | none => rfl
    | more x xs ih =>
      specialize ih ()
      dsimp only [Many.bind]
      rw [ih]
      rfl
  comp_map := by
    intro α β γ g h x
    dsimp [Functor.map]
    induction x with
    | none => rfl
    | more x xs ih =>
      specialize ih ()
      dsimp [Many.bind]
      rw [ih]
      rfl

/-- Many の Functor の実際の実装と思われるもの -/
def Many.map (f : α → β) : Many α → Many β
  | none => none
  | more x xs => more (f x) (fun () => Many.map f <| xs ())

def Many.two (x y : α) : Many α := .more x (fun () => .more y <| (fun () => .none))

example : (Many.map (· + 1) <| Many.one 1) = (· + 1) <$> Many.one 1 := by rfl

example : (Many.map (· + 1) <| Many.two 1 2) = (· + 1) <$> Many.two 1 2 := by rfl
