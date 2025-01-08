import LC.NV.UTLC.Sub.ReplaceVar
import LC.NV.UTLC.Sub.ReplaceFree


set_option autoImplicit false


open Term_


inductive are_alpha_equiv_v1 : Term_ → Term_ → Prop

| refl
  (M : Term_) :
  are_alpha_equiv_v1 M M

| symm
  (M N : Term_) :
  are_alpha_equiv_v1 M N →
  are_alpha_equiv_v1 N M

| trans
  (M N P : Term_) :
  are_alpha_equiv_v1 M N →
  are_alpha_equiv_v1 N P →
  are_alpha_equiv_v1 M P

| compat_app
  (M M' N N' : Term_) :
  are_alpha_equiv_v1 M M' →
  are_alpha_equiv_v1 N N' →
  are_alpha_equiv_v1 (app_ M N) (app_ M' N')

| compat_abs
  (x : Symbol_)
  (M M' : Term_) :
  are_alpha_equiv_v1 M M' →
  are_alpha_equiv_v1 (abs_ x M) (abs_ x M')

| replace
  (x y : Symbol_)
  (M : Term_) :
  y ∉ M.var_set →
  are_alpha_equiv_v1 (abs_ x M) (abs_ y (replace_var x y M))


-------------------------------------------------------------------------------


-- [2]

inductive are_alpha_equiv_v2 : Term_ → Term_ → Prop

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

| compat_app_left
  (M N L : Term_) :
  are_alpha_equiv_v2 M N →
  are_alpha_equiv_v2 (app_ M L) (app_ N L)

| compat_app_right
  (M N L : Term_) :
  are_alpha_equiv_v2 M N →
  are_alpha_equiv_v2 (app_ L M) (app_ L N)

| compat_abs
  (x : Symbol_)
  (M N : Term_) :
  are_alpha_equiv_v2 M N →
  are_alpha_equiv_v2 (abs_ x M) (abs_ x N)

| replace
  (x y : Symbol_)
  (M : Term_) :
  y ∉ M.var_set →
  are_alpha_equiv_v2 (abs_ x M) (abs_ y (replace_free x (var_ y) M))


------------------------------------------------------------------------------


lemma are_alpha_equiv_v1_replace_var_replace_free
  (u v : Symbol_)
  (e : Term_)
  (h1 : v ∉ e.var_set) :
  are_alpha_equiv_v1 (replace_var u v e) (replace_free u (var_ v) e) :=
  by
    induction e
    case var_ x =>
      unfold var_set at h1
      simp at h1
      unfold replace_var
      unfold replace_free
      split_ifs
      all_goals
        apply are_alpha_equiv_v1.refl
    case app_ M N ih_1 ih_2 =>
      unfold var_set at h1
      simp at h1
      obtain ⟨h1_left, h1_right⟩ := h1
      specialize ih_1 h1_left
      specialize ih_2 h1_right
      unfold replace_var
      unfold replace_free
      apply are_alpha_equiv_v1.compat_app
      · exact ih_1
      · exact ih_2
    case abs_ x M ih =>
      unfold var_set at h1
      simp at h1
      obtain ⟨h1_left, h1_right⟩ := h1
      specialize ih h1_left
      unfold replace_var
      unfold replace_free
      split_ifs
      case pos c1 =>
        subst c1
        obtain s1 := are_alpha_equiv_v1.replace u v M h1_left
        apply are_alpha_equiv_v1.symm
        exact s1
      case neg c1 =>
        apply are_alpha_equiv_v1.compat_abs
        exact ih


lemma are_alpha_equiv_v2_replace_free_replace_var
  (u v : Symbol_)
  (e : Term_)
  (h1 : v ∉ e.var_set) :
  are_alpha_equiv_v2 (replace_free u (var_ v) e) (replace_var u v e) :=
  by
    induction e
    case var_ x =>
      unfold var_set at h1
      simp at h1
      unfold replace_var
      unfold replace_free
      split_ifs
      all_goals
        apply are_alpha_equiv_v2.refl
    case app_ M N ih_1 ih_2 =>
      unfold var_set at h1
      simp at h1
      obtain ⟨h1_left, h1_right⟩ := h1
      specialize ih_1 h1_left
      specialize ih_2 h1_right
      unfold replace_var
      unfold replace_free
      obtain s1 := are_alpha_equiv_v2.compat_app_right _ _ _ ih_2
      obtain s2 := are_alpha_equiv_v2.compat_app_left (replace_free u (var_ v) M) (replace_var u v M) (replace_var u v N) ih_1
      apply are_alpha_equiv_v2.trans _ _ _ s1 s2
    case abs_ x M ih =>
      unfold var_set at h1
      simp at h1
      obtain ⟨h1_left, h1_right⟩ := h1
      specialize ih h1_left
      unfold replace_var
      unfold replace_free
      split_ifs
      case pos c1 =>
        subst c1
        obtain s1 := are_alpha_equiv_v2.replace u v M h1_left
        apply are_alpha_equiv_v2.trans (abs_ u M) (abs_ v (replace_free u (var_ v) M)) (abs_ v (replace_var u v M)) s1
        apply are_alpha_equiv_v2.compat_abs
        exact ih
      case neg c1 =>
        apply are_alpha_equiv_v2.compat_abs
        exact ih


lemma are_alpha_equiv_v1_imp_are_alpha_equiv_v2
  (e e' : Term_)
  (h1 : are_alpha_equiv_v1 e e') :
  are_alpha_equiv_v2 e e' :=
  by
    induction h1
    case refl M =>
      exact are_alpha_equiv_v2.refl M
    case symm M N _ ih_2 =>
      exact are_alpha_equiv_v2.symm M N ih_2
    case trans M N P _ _ ih_3 ih_4 =>
      exact are_alpha_equiv_v2.trans M N P ih_3 ih_4
    case compat_app M M' N N' _ _ ih_3 ih_4 =>
      obtain s1 := are_alpha_equiv_v2.compat_app_left M M' N ih_3
      obtain s2 := are_alpha_equiv_v2.compat_app_right N N' M' ih_4
      exact are_alpha_equiv_v2.trans (app_ M N) (app_ M' N) (app_ M' N') s1 s2
    case compat_abs x M M' _ ih_2 =>
      exact are_alpha_equiv_v2.compat_abs x M M' ih_2
    case replace x y M ih_1 =>
      obtain s1 := are_alpha_equiv_v2.replace x y M ih_1
      apply are_alpha_equiv_v2.trans (abs_ x M) (abs_ y (replace_free x (var_ y) M)) (abs_ y (replace_var x y M)) s1
      apply are_alpha_equiv_v2.compat_abs y (replace_free x (var_ y) M) (replace_var x y M)
      apply are_alpha_equiv_v2_replace_free_replace_var; exact ih_1


lemma are_alpha_equiv_v2_imp_are_alpha_equiv_v1
  (e e' : Term_)
  (h1 : are_alpha_equiv_v2 e e') :
  are_alpha_equiv_v1 e e' :=
  by
    induction h1
    case refl M =>
      exact are_alpha_equiv_v1.refl M
    case symm M N _ ih_2 =>
      exact are_alpha_equiv_v1.symm M N ih_2
    case trans M N P _ _ ih_3 ih_4 =>
      exact are_alpha_equiv_v1.trans M N P ih_3 ih_4
    case compat_app_left M N L _ ih_2 =>
      apply are_alpha_equiv_v1.compat_app M N L L
      · exact ih_2
      · exact are_alpha_equiv_v1.refl L
    case compat_app_right M N L _ ih_2 =>
      apply are_alpha_equiv_v1.compat_app L L M N
      · exact are_alpha_equiv_v1.refl L
      · exact ih_2
    case compat_abs x M N _ ih_2 =>
      exact are_alpha_equiv_v1.compat_abs x M N ih_2
    case replace x y M ih_1 =>
      obtain s1 := are_alpha_equiv_v1.replace x y M ih_1
      apply are_alpha_equiv_v1.trans _ _ _ s1
      apply are_alpha_equiv_v1.compat_abs
      apply are_alpha_equiv_v1_replace_var_replace_free; exact ih_1


lemma are_alpha_equiv_v1_iff_are_alpha_equiv_v2
  (e e' : Term_) :
  are_alpha_equiv_v1 e e' ↔ are_alpha_equiv_v2 e e' :=
  by
    constructor
    · exact are_alpha_equiv_v1_imp_are_alpha_equiv_v2 e e'
    · exact are_alpha_equiv_v2_imp_are_alpha_equiv_v1 e e'


-------------------------------------------------------------------------------


example
  (e e' : Term_)
  (h1 : are_alpha_equiv_v1 e e') :
  e.free_var_set = e'.free_var_set :=
  by
    induction h1
    case refl M =>
      exact Eq.refl M.free_var_set
    case symm M N _ ih_2 =>
      exact Eq.symm ih_2
    case trans M N P _ _ ih_3 ih_4 =>
      exact Eq.trans ih_3 ih_4
    case compat_app M M' N N' ih_1 ih_2 ih_3 ih_4 =>
      unfold Term_.free_var_set
      congr
    case compat_abs x M M' ih_1 ih_2 =>
      unfold Term_.free_var_set
      congr
    case replace x y M ih =>
      unfold Term_.free_var_set
      apply replace_var_free_var_set_sdiff; exact ih
