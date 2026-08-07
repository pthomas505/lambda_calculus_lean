

theorem neq_comm
  {α : Type}
  (x y : α) :
  (¬ x = y) ↔ (¬ y = x) :=
  by
  rewrite [Eq.comm]
  apply Iff.refl
