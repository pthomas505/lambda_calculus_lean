import TtfpLean.UTLC.Binders
import TtfpLean.UTLC.Sub.ReplaceFree
import TtfpLean.UTLC.Sub.ReplaceVar


set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.style.longLine false


/--
  `are_alpha_equiv_v1 M N` := True if and only if the terms `M` and `N` are alpha equivalent.
  Definition 1.5.2
-/
inductive are_alpha_equiv_v1 : Term_ → Term_ → Prop

| rename
  (x y : String)
  (M : Term_) :
  ¬ is_free_in y M →
  ¬ is_binder_in y M →
  are_alpha_equiv_v1 (Term_.Abs x M) (Term_.Abs y (replace_free x (Term_.Var y) M))

| compat_app_left
  (M M' L : Term_) :
  are_alpha_equiv_v1 M M' →
  are_alpha_equiv_v1 (Term_.App M L) (Term_.App M' L)

| compat_app_right
  (M M' L : Term_) :
  are_alpha_equiv_v1 M M' →
  are_alpha_equiv_v1 (Term_.App L M) (Term_.App L M')

| compat_abs
  (x : String)
  (M M' : Term_) :
  are_alpha_equiv_v1 M M' →
  are_alpha_equiv_v1 (Term_.Abs x M) (Term_.Abs x M')

| refl
  (M : Term_) :
  are_alpha_equiv_v1 M M

| symm
  (M N : Term_) :
  are_alpha_equiv_v1 M N →
  are_alpha_equiv_v1 N M

| trans
  (L M N : Term_) :
  are_alpha_equiv_v1 L M →
  are_alpha_equiv_v1 M N →
  are_alpha_equiv_v1 L N


/--
  `are_alpha_equiv_v2 M N` := True if and only if the terms `M` and `N` are alpha equivalent.
-/
inductive are_alpha_equiv_v2 : Term_ → Term_ → Prop

| rename
  (x y : String)
  (M : Term_) :
  ¬ occurs_in y M →
  are_alpha_equiv_v2 (Term_.Abs x M) (Term_.Abs y (replace_free x (Term_.Var y) M))

| compat_app_left
  (M M' L : Term_) :
  are_alpha_equiv_v2 M M' →
  are_alpha_equiv_v2 (Term_.App M L) (Term_.App M' L)

| compat_app_right
  (M M' L : Term_) :
  are_alpha_equiv_v2 M M' →
  are_alpha_equiv_v2 (Term_.App L M) (Term_.App L M')

| compat_abs
  (x : String)
  (M M' : Term_) :
  are_alpha_equiv_v2 M M' →
  are_alpha_equiv_v2 (Term_.Abs x M) (Term_.Abs x M')

| refl
  (M : Term_) :
  are_alpha_equiv_v2 M M

| symm
  (M N : Term_) :
  are_alpha_equiv_v2 M N →
  are_alpha_equiv_v2 N M

| trans
  (L M N : Term_) :
  are_alpha_equiv_v2 L M →
  are_alpha_equiv_v2 M N →
  are_alpha_equiv_v2 L N


/--
  `are_alpha_equiv_v3 M N` := True if and only if the terms `M` and `N` are alpha equivalent.
-/
inductive are_alpha_equiv_v3 : Term_ → Term_ → Prop

| rename
  (x y : String)
  (M : Term_) :
  ¬ occurs_in y M →
  are_alpha_equiv_v3 (Term_.Abs x M) (Term_.Abs y (replace_var x y M))

| compat_app
  (M M' N N' : Term_) :
  are_alpha_equiv_v3 M M' →
  are_alpha_equiv_v3 N N' →
  are_alpha_equiv_v3 (Term_.App M N) (Term_.App M' N')

| compat_abs
  (x : String)
  (M M' : Term_) :
  are_alpha_equiv_v3 M M' →
  are_alpha_equiv_v3 (Term_.Abs x M) (Term_.Abs x M')

| refl
  (M : Term_) :
  are_alpha_equiv_v3 M M

| symm
  (M N : Term_) :
  are_alpha_equiv_v3 M N →
  are_alpha_equiv_v3 N M

| trans
  (L M N : Term_) :
  are_alpha_equiv_v3 L M →
  are_alpha_equiv_v3 M N →
  are_alpha_equiv_v3 L N


-- ----------------------------------------------------------------------------


theorem are_alpha_equiv_v1_imp_are_alpha_equiv_v2
  (P Q : Term_)
  (h1 : are_alpha_equiv_v1 P Q) :
  are_alpha_equiv_v2 P Q :=
  by
  induction h1
  case rename x y M ih_1 ih_2 =>
    apply are_alpha_equiv_v2.rename
    rewrite [occurs_in_iff_is_binder_in_or_is_free_in]
    intro contra
    cases contra
    case inl contra =>
      contradiction
    case inr contra =>
      contradiction
  case compat_app_left M M' L ih_1 ih_2 =>
    apply are_alpha_equiv_v2.compat_app_left
    exact ih_2
  case compat_app_right M M' L ih_1 ih_2 =>
    apply are_alpha_equiv_v2.compat_app_right
    exact ih_2
  case compat_abs x M M' ih_1 ih_2 =>
    apply are_alpha_equiv_v2.compat_abs
    exact ih_2
  case refl M =>
    apply are_alpha_equiv_v2.refl
  case symm M N ih_1 ih_2 =>
    apply are_alpha_equiv_v2.symm
    exact ih_2
  case trans L M N ih_1 ih_2 ih_3 ih_4 =>
    exact are_alpha_equiv_v2.trans L M N ih_3 ih_4


theorem are_alpha_equiv_v2_imp_are_alpha_equiv_v1
  (P Q : Term_)
  (h1 : are_alpha_equiv_v2 P Q) :
  are_alpha_equiv_v1 P Q :=
  by
  induction h1
  case rename x y M ih =>
    apply are_alpha_equiv_v1.rename
    · intro contra
      apply ih
      rewrite [occurs_in_iff_is_binder_in_or_is_free_in]
      right
      exact contra
    · intro contra
      apply ih
      rewrite [occurs_in_iff_is_binder_in_or_is_free_in]
      left
      exact contra
  case compat_app_left M M' L ih_1 ih_2 =>
    apply are_alpha_equiv_v1.compat_app_left
    exact ih_2
  case compat_app_right M M' L ih_1 ih_2 =>
    apply are_alpha_equiv_v1.compat_app_right
    exact ih_2
  case compat_abs x M M' ih_1 ih_2 =>
    apply are_alpha_equiv_v1.compat_abs
    exact ih_2
  case refl M =>
    apply are_alpha_equiv_v1.refl
  case symm M N ih_1 ih_2 =>
    apply are_alpha_equiv_v1.symm
    exact ih_2
  case trans L M N ih_1 ih_2 ih_3 ih_4 =>
    exact are_alpha_equiv_v1.trans L M N ih_3 ih_4


theorem are_alpha_equiv_v1_iff_are_alpha_equiv_v2
  (P Q : Term_) :
  are_alpha_equiv_v1 P Q ↔ are_alpha_equiv_v2 P Q :=
  by
  constructor
  · apply are_alpha_equiv_v1_imp_are_alpha_equiv_v2
  · apply are_alpha_equiv_v2_imp_are_alpha_equiv_v1


-- ----------------------------------------------------------------------------


theorem are_alpha_equiv_v3_replace_var_replace_free
  (x y : String)
  (M : Term_)
  (h1 : ¬ occurs_in y M) :
  are_alpha_equiv_v3 (replace_var x y M) (replace_free x (Term_.Var y) M) :=
  by
  induction M
  case Var v =>
    unfold replace_var
    unfold replace_free
    apply are_alpha_equiv_v3.refl
  case App P Q ih_1 ih_2 =>
    unfold occurs_in at h1
    rewrite [not_or] at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    unfold replace_var
    unfold replace_free
    apply are_alpha_equiv_v3.compat_app
    · exact ih_1 h1_left
    · exact ih_2 h1_right
  case Abs v P ih =>
    unfold occurs_in at h1
    rewrite [not_or] at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    unfold replace_var
    unfold replace_free
    split
    case isTrue c1 =>
      rewrite [c1]
      apply are_alpha_equiv_v3.symm
      apply are_alpha_equiv_v3.rename
      exact h1_right
    case isFalse c1 =>
      apply are_alpha_equiv_v3.compat_abs
      exact ih h1_right


theorem are_alpha_equiv_v2_replace_free_replace_var
  (x y : String)
  (M : Term_)
  (h1 : ¬ occurs_in y M) :
  are_alpha_equiv_v2 (replace_free x (Term_.Var y) M) (replace_var x y M) :=
  by
  induction M
  case Var v =>
    unfold replace_var
    unfold replace_free
    apply are_alpha_equiv_v2.refl
  case App P Q ih_1 ih_2 =>
    unfold occurs_in at h1
    rewrite [not_or] at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    specialize ih_1 h1_left
    specialize ih_2 h1_right

    unfold replace_var
    unfold replace_free

    obtain s1 := are_alpha_equiv_v2.compat_app_right (replace_free x (Term_.Var y) Q) (replace_var x y Q) (replace_free x (Term_.Var y) P) ih_2

    obtain s2 := are_alpha_equiv_v2.compat_app_left (replace_free x (Term_.Var y) P) (replace_var x y P) (replace_var x y Q) ih_1

    apply are_alpha_equiv_v2.trans _ (Term_.App (replace_free x (Term_.Var y) P) (replace_var x y Q)) _
    · exact s1
    · exact s2
  case Abs v P ih =>
    unfold occurs_in at h1
    rewrite [not_or] at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    unfold replace_var
    unfold replace_free
    split
    case isTrue c1 =>
      rewrite [← c1]
      apply are_alpha_equiv_v2.trans (Term_.Abs x P) (Term_.Abs y (replace_free x (Term_.Var y) P)) (Term_.Abs y (replace_var x y P))
      · apply are_alpha_equiv_v2.rename
        exact h1_right
      · apply are_alpha_equiv_v2.compat_abs
        exact ih h1_right
    case isFalse c1 =>
      apply are_alpha_equiv_v2.compat_abs
      exact ih h1_right


theorem are_alpha_equiv_v3_imp_are_alpha_equiv_v2
  (P Q : Term_)
  (h1 : are_alpha_equiv_v3 P Q) :
  are_alpha_equiv_v2 P Q :=
  by
  induction h1
  case rename x y M ih =>
    apply are_alpha_equiv_v2.trans (Term_.Abs x M) (Term_.Abs y (replace_free x (Term_.Var y) M)) (Term_.Abs y (replace_var x y M))
    · apply are_alpha_equiv_v2.rename
      exact ih
    · apply are_alpha_equiv_v2.compat_abs
      apply are_alpha_equiv_v2_replace_free_replace_var
      exact ih
  case compat_app M M' N N' ih_1 ih_2 ih_3 ih_4 =>
    apply are_alpha_equiv_v2.trans (Term_.App M N) (Term_.App M' N) (Term_.App M' N')
    · apply are_alpha_equiv_v2.compat_app_left
      exact ih_3
    · apply are_alpha_equiv_v2.compat_app_right
      exact ih_4
  case compat_abs x M M' ih_1 ih_2 =>
    apply are_alpha_equiv_v2.compat_abs
    exact ih_2
  case refl M =>
    apply are_alpha_equiv_v2.refl
  case symm M N ih_1 ih_2 =>
    apply are_alpha_equiv_v2.symm
    exact ih_2
  case trans L M N ih_1 ih_2 ih_3 ih_4 =>
    exact are_alpha_equiv_v2.trans L M N ih_3 ih_4


theorem are_alpha_equiv_v2_imp_are_alpha_equiv_v3
  (P Q : Term_)
  (h1 : are_alpha_equiv_v2 P Q) :
  are_alpha_equiv_v3 P Q :=
  by
  induction h1
  case rename x y M ih =>
    apply are_alpha_equiv_v3.trans (Term_.Abs x M) (Term_.Abs y (replace_var x y M)) (Term_.Abs y (replace_free x (Term_.Var y) M))
    · apply are_alpha_equiv_v3.rename
      exact ih
    · apply are_alpha_equiv_v3.compat_abs
      apply are_alpha_equiv_v3_replace_var_replace_free
      exact ih
  case compat_app_left M M' L ih_1 ih_2 =>
    apply are_alpha_equiv_v3.compat_app
    · exact ih_2
    · apply are_alpha_equiv_v3.refl
  case compat_app_right M M' L ih_1 ih_2 =>
    apply are_alpha_equiv_v3.compat_app
    · apply are_alpha_equiv_v3.refl
    · exact ih_2
  case compat_abs x M M' ih_1 ih_2 =>
    apply are_alpha_equiv_v3.compat_abs
    exact ih_2
  case refl M =>
    apply are_alpha_equiv_v3.refl
  case symm M N ih_1 ih_2 =>
    apply are_alpha_equiv_v3.symm
    exact ih_2
  case trans L M N ih_1 ih_2 ih_3 ih_4 =>
    exact are_alpha_equiv_v3.trans L M N ih_3 ih_4


theorem are_alpha_equiv_v2_iff_are_alpha_equiv_v3
  (P Q : Term_) :
  are_alpha_equiv_v2 P Q ↔ are_alpha_equiv_v3 P Q :=
  by
  constructor
  · apply are_alpha_equiv_v2_imp_are_alpha_equiv_v3
  · apply are_alpha_equiv_v3_imp_are_alpha_equiv_v2


-- ----------------------------------------------------------------------------


example
  (P Q : Term_)
  (h1 : are_alpha_equiv_v2 P Q) :
  P.free_var_set = Q.free_var_set :=
  by
    rewrite [Finset.ext_iff]
    intro z
    simp only [← is_free_in_iff_mem_free_var_set]
    induction h1
    case rename x y M ih =>
      rewrite [occurs_in_iff_is_binder_in_or_is_free_in] at ih
      rewrite [not_or] at ih
      obtain ⟨ih_left, ih_right⟩ := ih

      unfold is_free_in
      constructor
      · intro a1
        obtain ⟨a1_left, a1_right⟩ := a1
        constructor
        · intro contra
          apply ih_right
          rewrite [← contra]
          exact a1_right
        · exact is_free_in_replace_free_ne_1 x (Term_.Var y) M z a1_left a1_right
      · intro a1
        obtain ⟨a1_left, a1_right⟩ := a1
        constructor
        · intro contra
          rewrite [contra] at a1_right
          apply a1_left
          rewrite [contra]
          exact is_free_in_replace_free_eq_var_2 x y M a1_right
        · by_contra contra
          obtain s1 := is_free_in_replace_free_ne_2 x (Term_.Var y) M z a1_right contra
          unfold is_free_in at s1
          contradiction
    case compat_app_left M M' L ih_1 ih_2 =>
      unfold is_free_in
      rewrite [ih_2]
      apply Iff.refl
    case compat_app_right M M' L ih_1 ih_2 =>
      unfold is_free_in
      rewrite [ih_2]
      apply Iff.refl
    case compat_abs x M M' ih_1 ih_2 =>
      unfold is_free_in
      rewrite [ih_2]
      apply Iff.refl
    case refl M =>
      apply Iff.refl
    case symm M N ih_1 ih_2 =>
      exact Iff.symm ih_2
    case trans L M N ih_1 ih_2 ih_3 ih_4 =>
      exact Iff.trans ih_3 ih_4


-- ----------------------------------------------------------------------------


example :
  are_alpha_equiv_v2
    (Term_| ((λ x. (x (λ z. (x y)))) z))
    (Term_| ((λ x. (x (λ z. (x y)))) z)) :=
  by
  apply are_alpha_equiv_v2.refl


example :
  are_alpha_equiv_v2
    (Term_| ((λ x. (x (λ z. (x y)))) z))
    (Term_| ((λ u. (u (λ z. (u y)))) z)) :=
  by
  apply are_alpha_equiv_v2.compat_app_left
  apply are_alpha_equiv_v2.rename
  simp only [occurs_in]
  simp only [String.reduceEq]
  tauto


example :
  are_alpha_equiv_v2
    (Term_| ((λ x. (x (λ z. (x y)))) z))
    (Term_| ((λ z. (z (λ x. (z y)))) z)) :=
  by
    apply are_alpha_equiv_v2.compat_app_left
    have s1 : are_alpha_equiv_v2
      (Term_| (λ x. (x (λ z. (x y)))))
      (Term_| (λ w. (w (λ z. (w y))))) :=
    by
      apply are_alpha_equiv_v2.rename
      simp only [occurs_in]
      simp only [String.reduceEq]
      tauto
    have s2 : are_alpha_equiv_v2
      (Term_| (λ w. (w (λ z. (w y)))))
      (Term_| (λ w. (w (λ x. (w y))))) :=
    by
      apply are_alpha_equiv_v2.compat_abs
      apply are_alpha_equiv_v2.compat_app_right
      apply are_alpha_equiv_v2.rename
      simp only [occurs_in]
      simp only [String.reduceEq]
      tauto
    have s3 : are_alpha_equiv_v2
      (Term_| (λ w. (w (λ x. (w y)))))
      (Term_| (λ z. (z (λ x. (z y))))) :=
    by
      apply are_alpha_equiv_v2.rename
      simp only [occurs_in]
      simp only [String.reduceEq]
      tauto
    apply are_alpha_equiv_v2.trans _ (Term_| (λ w. (w (λ x. (w y)))))
    · apply are_alpha_equiv_v2.trans _ (Term_| (λ w. (w (λ z. (w y)))))
      · exact s1
      · exact s2
    · exact s3


example :
  are_alpha_equiv_v2
  (Term_| (λ x. (λ y. ((x z) y))))
  (Term_| (λ v. (λ y. ((v z) y)))) :=
  by
  apply are_alpha_equiv_v2.rename
  simp only [occurs_in]
  simp only [String.reduceEq]
  tauto


example :
  are_alpha_equiv_v2
  (Term_| (λ x. (λ y. ((x z) y))))
  (Term_| (λ v. (λ u. ((v z) u)))) :=
  by
  apply are_alpha_equiv_v2.trans _ (Term_| (λ v. (λ y. ((v z) y))))
  · apply are_alpha_equiv_v2.rename
    simp only [occurs_in]
    simp only [String.reduceEq]
    tauto
  · apply are_alpha_equiv_v2.compat_abs
    apply are_alpha_equiv_v2.rename
    simp only [occurs_in]
    simp only [String.reduceEq]
    tauto
