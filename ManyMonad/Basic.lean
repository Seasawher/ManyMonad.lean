/-- lazy analogy of list.
see <https://lean-lang.org/functional_programming_in_lean/monads/arithmetic.html#nondeterministic-search> -/
inductive Many (α : Type) where
  | none : Many α
  | more : α → (Unit → Many α) → Many α

def Many.one (x : α) : Many α := Many.more x (fun () => Many.none)

def Many.union : Many α → Many α → Many α
  | Many.none, ys => ys
  | Many.more x xs, ys => Many.more x (fun () => union (xs ()) ys)

instance : Append (Many α) where
  append := Many.union

/-! Many を eval 可能にする -/

def Many.takeAll : Many α → List α
  | Many.none => []
  | Many.more x xs => x :: (xs ()).takeAll

instance [ToString α] : ToString (Many α) where
  toString m := toString (Many.takeAll m)

/-! Many を Monad にする -/

def Many.bind : Many α → (α → Many β) → Many β
  | Many.none, _ =>
    Many.none
  | Many.more x xs, f =>
    (f x) ++ (bind (xs ()) f)

instance : Monad Many where
  pure := Many.one
  bind := Many.bind
