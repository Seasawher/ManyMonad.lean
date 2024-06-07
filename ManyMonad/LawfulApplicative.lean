import ManyMonad.LawfulFunctor

variable {α β : Type}

namespace Many
open Many

def seq (fs : Many (α → β)) (xs : Unit → Many α) : Many β :=
  match fs with
  | none => none
  | more f fs => f <$> (xs ()) ++ seq (fs ()) xs

@[match_pattern]
def cons (x : α) (xs : Many α) : Many α :=
  .more x (fun () => xs)

theorem union_eq_more_cons (x : α) (xs : Unit → Many α) (ys : Many α) :
  .more x xs ++ ys = cons x (union (xs ()) ys):= by rfl

@[simp] theorem none_union (xs : Many α) : none ++ xs = xs := by
  rfl

@[simp] theorem union_none (x : α) (xs : Many α) : xs ++ none = xs := by
  induction xs with
  | none => rfl
  | more x xs ih =>
    sorry

theorem seq_def (fs : Many (α → β)) (xs : Unit → Many α) :
    Many.seq fs xs = fs <*> xs () := by
  induction fs with
  | none => rfl
  | more f fs ih =>
    specialize ih ()
    dsimp [seq]
    sorry

end Many
