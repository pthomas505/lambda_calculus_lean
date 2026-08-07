import TtfpLean.UTLC.Sub.ReplaceFree

import TtfpLean.Extra


set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.style.longLine false


/--
  `sub_is_def_v3 M x N` := True if and only if `M [ x := N ]` is defined
-/
inductive sub_is_def_v3 : Term_ → String → Term_ → Prop

-- y [ x := N ] is defined
| var
  (y : String)
  (x : String)
  (N : Term_) :
  sub_is_def_v3 (Term_.Var y) x N

-- P [ x := N ] is defined → Q [ x := N ] is defined → (P Q) [ x := N ] is defined
| app
  (P : Term_)
  (Q : Term_)
  (x : String)
  (N : Term_) :
  sub_is_def_v3 P x N →
  sub_is_def_v3 Q x N →
  sub_is_def_v3 (Term_.App P Q) x N

-- x = y → ( λ y . P ) [ x := N ] is defined
| abs_1
  (y : String)
  (P : Term_)
  (x : String)
  (N : Term_) :
  x = y →
  sub_is_def_v3 (Term_.Abs y P) x N

| abs_2
  (y : String)
  (P : Term_)
  (x : String)
  (N : Term_) :
  ¬ x = y →
  ¬ is_free_in x P →
  sub_is_def_v3 (Term_.Abs y P) x N

| abs_3
  (y : String)
  (P : Term_)
  (x : String)
  (N : Term_) :
  ¬ x = y →
  ¬ is_free_in y N →
  sub_is_def_v3 P x N →
  sub_is_def_v3 (Term_.Abs y P) x N


-- ----------------------------------------------------------------------------


/--
  `sub_is_def_v3_alt x N M` := True if and only if `M [ x := N ]` is defined
-/
inductive sub_is_def_v3_alt : String → Term_ → Term_ → Prop

-- y [ x := N ] is defined
| var
  (x : String)
  (N : Term_)
  (y : String) :
  sub_is_def_v3_alt x N (Term_.Var y)

-- P [ x := N ] is defined → Q [ x := N ] is defined → (P Q) [ x := N ] is defined
| app
  (x : String)
  (N : Term_)
  (P : Term_)
  (Q : Term_) :
  sub_is_def_v3_alt x N P →
  sub_is_def_v3_alt x N Q →
  sub_is_def_v3_alt x N (Term_.App P Q)

-- x = y → ( λ y . P ) [ x := N ] is defined
| abs_1
  (x : String)
  (N : Term_)
  (y : String)
  (P : Term_) :
  x = y →
  sub_is_def_v3_alt x N (Term_.Abs y P)

| abs_2
  (x : String)
  (N : Term_)
  (y : String)
  (P : Term_) :
  ¬ x = y →
  ¬ is_free_in x P →
  sub_is_def_v3_alt x N (Term_.Abs y P)

| abs_3
  (x : String)
  (N : Term_)
  (y : String)
  (P : Term_) :
  ¬ x = y →
  ¬ is_free_in y N →
  sub_is_def_v3_alt x N P →
  sub_is_def_v3_alt x N (Term_.Abs y P)


example
  (M : Term_)
  (x : String)
  (N : Term_)
  (h1 : sub_is_def_v3 M x N) :
  sub_is_def_v3_alt x N M :=
  by
  induction h1
  case var y =>
    apply sub_is_def_v3_alt.var
  case app P_ Q_ x_ N_ ih_1 ih_2 ih_3 ih_4 =>
    apply sub_is_def_v3_alt.app
    · exact ih_3
    · exact ih_4
  case abs_1 y_ P_ x_ N_ ih =>
    apply sub_is_def_v3_alt.abs_1
    exact ih
  case abs_2 y_ P_ x_ N_ ih_1 ih_2 =>
    apply sub_is_def_v3_alt.abs_2
    · exact ih_1
    · exact ih_2
  case abs_3 y_ P_ x_ N_ ih_1 ih_2 ih_3 ih_4 =>
    apply sub_is_def_v3_alt.abs_3
    · exact ih_1
    · exact ih_2
    · exact ih_4


example
  (x : String)
  (N : Term_)
  (M : Term_)
  (h1 : sub_is_def_v3_alt x N M) :
  sub_is_def_v3 M x N :=
  by
  induction h1
  case var y =>
    apply sub_is_def_v3.var
  case app P_ Q_ ih_1 ih_2 =>
    apply sub_is_def_v3.app
    · exact ih_1
    · exact ih_2
  case abs_1 y_ P_ ih =>
    apply sub_is_def_v3.abs_1
    exact ih
  case abs_2 y_ P_ ih_1 ih_2 =>
    apply sub_is_def_v3.abs_2
    · exact ih_1
    · exact ih_2
  case abs_3 y_ P_ ih_1 ih_2 ih_3 ih_4 =>
    apply sub_is_def_v3.abs_3
    · exact ih_1
    · exact ih_2
    · exact ih_4


-- ----------------------------------------------------------------------------


theorem not_is_free_in_sub_is_def
  (x : String)
  (N : Term_)
  (M : Term_)
  (h1 : ¬ is_free_in x M) :
  sub_is_def_v3_alt x N M :=
  by
    induction M
    case Var v =>
      apply sub_is_def_v3_alt.var
    case App P Q ih_1 ih_2 =>
      unfold is_free_in at h1
      rewrite [not_or] at h1
      obtain ⟨h1_left, h1_right⟩ := h1

      apply sub_is_def_v3_alt.app
      · exact ih_1 h1_left
      · exact ih_2 h1_right
    case Abs v P ih =>
      by_cases c1 : x = v
      · apply sub_is_def_v3_alt.abs_1
        exact c1
      · apply sub_is_def_v3_alt.abs_2
        · exact c1
        · unfold is_free_in at h1
          rewrite [not_and] at h1
          exact h1 c1


-- ----------------------------------------------------------------------------


theorem sub_is_def_var_eq
  (M : Term_)
  (x : String) :
  sub_is_def_v3_alt x (Term_.Var x) M :=
  by
    induction M
    case Var v =>
      apply sub_is_def_v3_alt.var
    case App P Q ih_1 ih_2 =>
      apply sub_is_def_v3_alt.app
      · exact ih_1
      · exact ih_2
    case Abs v P ih =>
      by_cases c1 : x = v
      · rewrite [c1]
        apply sub_is_def_v3_alt.abs_1
        apply Eq.refl
      · apply sub_is_def_v3_alt.abs_3
        · exact c1
        · unfold is_free_in
          intro contra
          apply c1
          rewrite [contra]
          apply Eq.refl
        · exact ih


-- ----------------------------------------------------------------------------


theorem sub_is_def_is_free_in_replace_free
  (x : String)
  (N : Term_)
  (M : Term_)
  (z : String)
  (h1 : is_free_in z N)
  (h2 : is_free_in x M)
  (h3 : sub_is_def_v3_alt x N M) :
  is_free_in z (replace_free x N M) :=
  by
  induction h3
  case var y_ =>
    unfold is_free_in at h2

    unfold replace_free
    split
    case isTrue c1 =>
      exact h1
    case isFalse c1 =>
      contradiction
  case app P_ Q_ ih_1 ih_2 ih_3 ih_4 =>
    unfold is_free_in at h2

    unfold replace_free
    unfold is_free_in
    cases h2
    case inl h2 =>
      left
      exact ih_3 h2
    case inr h2 =>
      right
      exact ih_4 h2
  case abs_1 y_ P_ ih =>
    unfold is_free_in at h2
    obtain ⟨h2_left, h2_right⟩ := h2
    contradiction
  case abs_2 y_ P_ ih_1 ih_2 =>
    unfold is_free_in at h2
    obtain ⟨h2_left, h2_right⟩ := h2
    contradiction
  case abs_3 y_ P_ ih_1 ih_2 ih_3 ih_4 =>
    unfold is_free_in at h2
    obtain ⟨h2_left, h2_right⟩ := h2

    unfold replace_free
    split
    case isTrue c1 =>
      contradiction
    case isFalse c1 =>
      unfold is_free_in
      constructor
      · intro contra
        apply ih_2
        rewrite [← contra]
        exact h1
      · exact ih_4 h2_right


-- ----------------------------------------------------------------------------


/-
  Since `x` is not free in `L`, every free occurrence of `x` in `replace_free y L M` occurs in `M`. Therefore `sub_is_def_v3_alt x N M` implies `sub_is_def_v3_alt x N (replace_free y L M)`.
-/
theorem sub_is_def_to_sub_is_def_replace_free
  (M N L : Term_)
  (x y : String)
  (h1 : sub_is_def_v3_alt x N M)
  (h2 : ¬ is_free_in x L) :
  sub_is_def_v3_alt x N (replace_free y L M) :=
  by
  induction M
  case Var v =>
    unfold replace_free
    split
    case isTrue c1 =>
      apply not_is_free_in_sub_is_def
      exact h2
    case isFalse c1 =>
      exact h1
  case App P Q ih_1 ih_2 =>
    cases h1
    case app c1 c2 =>
      apply sub_is_def_v3_alt.app
      · exact ih_1 c1
      · exact ih_2 c2
  case Abs v P ih =>
    simp only [replace_free]
    split
    case isTrue c1 =>
      exact h1
    case isFalse c1 =>
      cases h1
      case abs_1 c2 =>
        apply sub_is_def_v3_alt.abs_1
        exact c2
      case abs_2 c2 c3 =>
        apply sub_is_def_v3_alt.abs_2
        · exact c2
        · intro contra
          apply h2
          exact is_free_in_replace_free_ne_2 y L P x contra c3
      case abs_3 c2 c3 c4 =>
        apply sub_is_def_v3_alt.abs_3
        · exact c2
        · exact c3
        · exact ih c4


/-
  Since `¬ x = y`, no free occurrence of `x` in `M` is replaced in `replace_free y L M`. That is, every free occurrence of `x` in `M` occurs in `replace_free y L M`. Therefore `sub_is_def_v3_alt x N (replace_free y L M)` implies `sub_is_def_v3_alt x N M`.
-/
theorem sub_is_def_replace_free_to_sub_is_def
  (M N L : Term_)
  (x y : String)
  (h1 : sub_is_def_v3_alt x N (replace_free y L M))
  (h2 : ¬ x = y) :
  sub_is_def_v3_alt x N M :=
  by
  induction M
  case Var v =>
    apply sub_is_def_v3_alt.var
  case App P Q ih_1 ih_2 =>
    unfold replace_free at h1
    cases h1
    case app c1 c2 =>
      apply sub_is_def_v3_alt.app
      · exact ih_1 c1
      · exact ih_2 c2
  case Abs v P ih =>
    unfold replace_free at h1
    split at h1
    case isTrue c1 =>
      exact h1
    case isFalse c1 =>
      cases h1
      case abs_1 c2 =>
        apply sub_is_def_v3_alt.abs_1
        exact c2
      case abs_2 c2 c3 =>
        apply sub_is_def_v3_alt.abs_2
        · exact c2
        · intro contra
          apply c3
          apply is_free_in_replace_free_ne_1
          · exact h2
          · exact contra
      case abs_3 c2 c3 c4 =>
        apply sub_is_def_v3_alt.abs_3
        · exact c2
        · exact c3
        · exact ih c4


-- ----------------------------------------------------------------------------


theorem sub_is_def_and_is_free_in_imp_is_free_in
  (M N L : Term_)
  (x : String)
  (h1 : sub_is_def_v3_alt x N M)
  (h2 : ∀ (y : String), is_free_in y L → is_free_in y N) :
  sub_is_def_v3_alt x L M :=
  by
  induction M
  case Var v =>
    apply sub_is_def_v3_alt.var
  case App P Q ih_1 ih_2 =>
    cases h1
    case app c1 c2 =>
      apply sub_is_def_v3_alt.app
      · exact ih_1 c1
      · exact ih_2 c2
  case Abs v P ih =>
    cases h1
    case abs_1 c1 =>
      apply sub_is_def_v3_alt.abs_1
      exact c1
    case abs_2 c1 c2 =>
      apply sub_is_def_v3_alt.abs_2
      · exact c1
      · exact c2
    case abs_3 c1 c2 c3 =>
      apply sub_is_def_v3_alt.abs_3
      · exact c1
      · intro contra
        apply c2
        apply h2
        exact contra
      · apply ih
        exact c3


-- ----------------------------------------------------------------------------


theorem sub_is_def_to_sub_is_def_abs
  (x : String)
  (N : Term_)
  (M : Term_)
  (z : String)
  (h1 : sub_is_def_v3_alt x N M)
  (h2 : ¬ is_free_in z N) :
  sub_is_def_v3_alt x N (Term_.Abs z M) :=
  by
  by_cases c1 : x = z
  · rewrite [c1]
    apply not_is_free_in_sub_is_def
    unfold is_free_in
    rewrite [not_and]
    intro a1
    contradiction
  · apply sub_is_def_v3_alt.abs_3
    · exact c1
    · exact h2
    · exact h1


theorem sub_is_def_abs_to_sub_is_def
  (x : String)
  (N : Term_)
  (M : Term_)
  (z : String)
  (h1 : sub_is_def_v3_alt x N (Term_.Abs z M))
  (h2 : ¬ x = z) :
  sub_is_def_v3_alt x N M :=
  by
  cases h1
  case abs_1 c1 =>
    contradiction
  case abs_2 c1 c2 =>
    apply not_is_free_in_sub_is_def
    exact c2
  case abs_3 c1 c2 c3 =>
    exact c3
