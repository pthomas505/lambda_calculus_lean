import LambdaCalculusLean.NV.UTLC.Binders


set_option linter.style.docString false
set_option linter.style.longLine false
set_option linter.style.emptyLine false


/--
  `replace_free x N M` := The simultaneous replacement of each free occurrence of the variable `x` in the term `M` by the term `N`.
-/
def replace_free
  (x : String)
  (N : Term_) :
  Term_ → Term_
  | Term_.Var v =>
    if x = v
    then N
    else Term_.Var v

  | Term_.App P Q =>
    Term_.App (replace_free x N P) (replace_free x N Q)

  | Term_.Abs v P =>
    if x = v
    then Term_.Abs v P
    else Term_.Abs v (replace_free x N P)


-- ----------------------------------------------------------------------------


theorem not_is_free_in_replace_free
  (x : String)
  (N : Term_)
  (M : Term_)
  (h1 : ¬ is_free_in x M) :
  replace_free x N M = M :=
  by
  induction M
  case Var v =>
    unfold is_free_in at h1

    unfold replace_free
    split
    case isTrue c1 =>
      contradiction
    case isFalse c1 =>
      apply Eq.refl
  case App P Q ih_1 ih_2 =>
    unfold is_free_in at h1
    rewrite [not_or] at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    unfold replace_free
    rewrite [ih_1 h1_left]
    rewrite [ih_2 h1_right]
    apply Eq.refl
  case Abs v P ih =>
    unfold replace_free
    split
    case isTrue c1 =>
      apply Eq.refl
    case isFalse c1 =>
      unfold is_free_in at h1
      rewrite [not_and] at h1
      specialize h1 c1
      rewrite [ih h1]
      apply Eq.refl


-- ----------------------------------------------------------------------------


theorem is_free_in_replace_free_eq_1
  (x : String)
  (N : Term_)
  (M : Term_)
  (h1 : is_free_in x (replace_free x N M)) :
  is_free_in x M :=
  by
  induction M
  case Var v =>
    unfold replace_free at h1
    split at h1
    case isTrue c1 =>
      unfold is_free_in
      exact c1
    case isFalse c1 =>
      exact h1
  case App P Q ih_1 ih_2 =>
    unfold replace_free at h1
    unfold is_free_in at h1

    unfold is_free_in
    cases h1
    case inl h1 =>
      left
      exact ih_1 h1
    case inr h1 =>
      right
      exact ih_2 h1
  case Abs v P ih =>
    unfold replace_free at h1
    split at h1
    case isTrue c1 =>
      exact h1
    case isFalse c1 =>
      unfold is_free_in at h1
      obtain ⟨h1_left, h1_right⟩ := h1

      unfold is_free_in
      constructor
      · exact h1_left
      · exact ih h1_right


theorem is_free_in_replace_free_eq_2
  (x : String)
  (N : Term_)
  (M : Term_)
  (h1 : is_free_in x (replace_free x N M)) :
  is_free_in x N :=
  by
  induction M
  case Var v =>
    unfold replace_free at h1
    split at h1
    case isTrue c1 =>
      exact h1
    case isFalse c1 =>
      unfold is_free_in at h1
      contradiction
  case App P Q ih_1 ih_2 =>
    unfold replace_free at h1
    unfold is_free_in at h1

    cases h1
    case inl h1 =>
      exact ih_1 h1
    case inr h1 =>
      exact ih_2 h1
  case Abs v P ih =>
    unfold replace_free at h1
    split at h1
    case isTrue c1 =>
      unfold is_free_in at h1
      obtain ⟨h1_left, h1_right⟩ := h1
      contradiction
    case isFalse c1 =>
      unfold is_free_in at h1
      obtain ⟨h1_left, h1_right⟩ := h1
      exact ih h1_right


theorem is_free_in_replace_free_eq_3
  (x : String)
  (N : Term_)
  (M : Term_)
  (h1 : is_free_in x N)
  (h2 : is_free_in x M) :
  is_free_in x (replace_free x N M) :=
  by
  induction M
  case Var v =>
    unfold is_free_in at h2

    unfold replace_free
    split
    case isTrue c1 =>
      exact h1
    case isFalse c1 =>
      contradiction
  case App P Q ih_1 ih_2 =>
    unfold is_free_in at h2

    unfold replace_free
    unfold is_free_in
    cases h2
    case inl h2 =>
      left
      exact ih_1 h2
    case inr h2 =>
      right
      exact ih_2 h2
  case Abs v P ih =>
    unfold is_free_in at h2
    obtain ⟨h2_left, h2_right⟩ := h2

    unfold replace_free
    split
    case isTrue c1 =>
      contradiction
    case isFalse c1 =>
      unfold is_free_in
      constructor
      · exact h2_left
      · exact ih h2_right


-- ----------------------------------------------------------------------------


theorem is_free_in_replace_free_ne_1
  (x : String)
  (N : Term_)
  (M : Term_)
  (z : String)
  (h1 : ¬ z = x)
  (h2 : is_free_in z M) :
  is_free_in z (replace_free x N M) :=
  by
  induction M
  case Var v =>
    unfold is_free_in at h2

    unfold replace_free
    split
    case isTrue c1 =>
      rewrite [h2] at h1
      rewrite [c1] at h1
      contradiction
    case isFalse c1 =>
      unfold is_free_in
      exact h2
  case App P Q ih_1 ih_2 =>
    unfold is_free_in at h2

    unfold replace_free
    unfold is_free_in
    cases h2
    case inl h2 =>
      left
      exact ih_1 h2
    case inr h2 =>
      right
      exact ih_2 h2
  case Abs v P ih =>
    unfold replace_free
    split
    case isTrue c1 =>
      exact h2
    case isFalse c1 =>
      unfold is_free_in at h2
      obtain ⟨h2_left, h2_right⟩ := h2
      unfold is_free_in
      constructor
      · exact h2_left
      · exact ih h2_right


theorem is_free_in_replace_free_ne_2
  (x : String)
  (N : Term_)
  (M : Term_)
  (z : String)
  (h1 : is_free_in z (replace_free x N M))
  (h2 : ¬ is_free_in z M) :
  is_free_in z N :=
  by
  induction M
  case Var v =>
    unfold replace_free at h1

    unfold is_free_in at h2

    split at h1
    case isTrue c1 =>
      exact h1
    case isFalse c1 =>
      unfold is_free_in at h1
      contradiction
  case App P Q ih_1 ih_2 =>
    unfold replace_free at h1
    unfold is_free_in at h1

    unfold is_free_in at h2
    rewrite [not_or] at h2
    obtain ⟨h2_left, h2_right⟩ := h2

    cases h1
    case inl h1 =>
      exact ih_1 h1 h2_left
    case inr h1 =>
      exact ih_2 h1 h2_right
  case Abs v P ih =>
    unfold replace_free at h1
    split at h1
    case isTrue c1 =>
      contradiction
    case isFalse c1 =>
      unfold is_free_in at h1
      obtain ⟨h1_left, h1_right⟩ := h1

      unfold is_free_in at h2
      rewrite [not_and] at h2
      specialize h2 h1_left

      exact ih h1_right h2


theorem is_free_in_replace_free_ne_3
  (x : String)
  (N : Term_)
  (M : Term_)
  (z : String)
  (h1 : is_free_in z (replace_free x N M))
  (h2 : ¬ is_free_in z M) :
  is_free_in x M :=
  by
  induction M
  case Var v =>
    unfold replace_free at h1

    unfold is_free_in
    split at h1
    case isTrue c1 =>
      exact c1
    case isFalse c1 =>
      contradiction
  case App P Q ih_1 ih_2 =>
    unfold replace_free at h1
    unfold is_free_in at h1

    unfold is_free_in at h2
    rewrite [not_or] at h2
    obtain ⟨h2_left, h2_right⟩ := h2

    unfold is_free_in
    cases h1
    case inl h1 =>
      left
      exact ih_1 h1 h2_left
    case inr h1 =>
      right
      exact ih_2 h1 h2_right
  case Abs v P ih =>
    unfold replace_free at h1

    split at h1
    case isTrue c1 =>
      contradiction
    case isFalse c1 =>
      unfold is_free_in at h1
      obtain ⟨h1_left, h1_right⟩ := h1

      unfold is_free_in at h2
      rewrite [not_and] at h2
      specialize h2 h1_left

      unfold is_free_in
      constructor
      · exact c1
      · exact ih h1_right h2


-- ----------------------------------------------------------------------------


theorem replace_free_var_eq
  (x : String)
  (M : Term_) :
  replace_free x (Term_.Var x) M = M :=
  by
  induction M
  case Var v =>
    unfold replace_free
    split
    case isTrue c1 =>
      rewrite [c1]
      apply Eq.refl
    case isFalse c1 =>
      apply Eq.refl
  case App P Q ih_1 ih_2 =>
    unfold replace_free
    rewrite [ih_1]
    rewrite [ih_2]
    apply Eq.refl
  case Abs v P ih =>
    unfold replace_free
    split
    case isTrue c1 =>
      apply Eq.refl
    case isFalse c1 =>
      rewrite [ih]
      apply Eq.refl


-- ----------------------------------------------------------------------------


theorem is_free_in_replace_free_eq_var_1
  (x : String)
  (y : String)
  (M : Term_)
  (h1 : is_free_in x (replace_free x (Term_.Var y) M)) :
  is_free_in x M :=
  by
  exact is_free_in_replace_free_eq_1 x (Term_.Var y) M h1


theorem is_free_in_replace_free_eq_var_2
  (x : String)
  (y : String)
  (M : Term_)
  (h1 : is_free_in x (replace_free x (Term_.Var y) M)) :
  x = y :=
  by
  obtain s1 := is_free_in_replace_free_eq_2 x (Term_.Var y) M h1
  unfold is_free_in at s1
  exact s1


theorem is_free_in_replace_free_ne_var_1
  (x : String)
  (y : String)
  (M : Term_)
  (z : String)
  (h1 : ¬ z = x)
  (h2 : is_free_in z M) :
  is_free_in z (replace_free x (Term_.Var y) M) :=
  by
  exact is_free_in_replace_free_ne_1 x (Term_.Var y) M z h1 h2


theorem is_free_in_replace_free_ne_var_2
  (x : String)
  (y : String)
  (M : Term_)
  (z : String)
  (h1 : is_free_in z (replace_free x (Term_.Var y) M))
  (h2 : ¬ is_free_in z M) :
  z = y :=
  by
  obtain s1 := is_free_in_replace_free_ne_2 x (Term_.Var y) M z h1 h2
  unfold is_free_in at s1
  exact s1


theorem is_free_in_replace_free_ne_var_3
  (x : String)
  (y : String)
  (M : Term_)
  (z : String)
  (h1 : is_free_in z (replace_free x (Term_.Var y) M))
  (h2 : ¬ is_free_in z M) :
  is_free_in x M :=
  by
  exact is_free_in_replace_free_ne_3 x (Term_.Var y) M z h1 h2
