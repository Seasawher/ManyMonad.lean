import ManyMonad.Basic

variable {α β : Type}

/-- Many の Functor の実装 -/
def Many.map (f : α → β) : Many α → Many β
  | none => none
  | more x xs => more (f x) (fun () => Many.map f <| xs ())

/-- Monad インスタンスから誘導される実装と，上記の実装が一致する -/
@[simp] theorem Many.map_def (f : α → β) : f <$> x = Many.map f x := by
  induction x with
  | none => rfl
  | more x xs ih =>
    specialize ih ()
    simp [Many.map]
    rw [← ih]
    rfl

/-- Many は Functor 則を満たす -/
instance : LawfulFunctor Many where
  map_const := by
    intro α β
    rfl

  id_map := by
    intro α x
    simp only [Many.map_def]
    induction x with
    | none => rfl
    | more x xs ih =>
      specialize ih ()
      dsimp only [Many.map]
      rw [ih]
      rfl

  comp_map := by
    intro α β γ g h x
    simp only [Many.map_def]
    induction x with
    | none => rfl
    | more x xs ih =>
      specialize ih ()
      dsimp only [Many.map, Function.comp_apply]
      rw [ih]
