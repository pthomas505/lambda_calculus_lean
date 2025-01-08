import LC.NV.UTLC.Sub.Alpha
import LC.NV.UTLC.Sub.SubIsDef


set_option autoImplicit false


open Term_


inductive is_sub_v1 : Term_ → Symbol_ → Term_ → Term_ → Prop

-- if x = y then y [ x := N ] = N
| var_same
  (y : Symbol_)
  (x : Symbol_)
  (N : Term_) :
  x = y →
  is_sub_v1 (var_ y) x N N

-- if x ≠ y then y [ x := N ] = y
| var_diff
  (y : Symbol_)
  (x : Symbol_)
  (N : Term_) :
  ¬ x = y →
  is_sub_v1 (var_ y) x N (var_ y)

-- (P Q) [ x := N ] = (P [ x := N ] Q [ x := N ])
| app
  (P : Term_)
  (Q : Term_)
  (x : Symbol_)
  (N : Term_)
  (P' : Term_)
  (Q' : Term_) :
  is_sub_v1 P x N P' →
  is_sub_v1 Q x N Q' →
  is_sub_v1 (app_ P Q) x N (app_ P' Q')

| abs_1
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_) :
  x ∉ (abs_ y P).free_var_set →
  is_sub_v1 (abs_ y P) x N (abs_ y P)

| abs_2
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_)
  (P' : Term_) :
  ¬ x = y →
  y ∉ N.free_var_set →
  is_sub_v1 P x N P' →
  is_sub_v1 (abs_ y P) x N (abs_ y P')


-------------------------------------------------------------------------------


inductive is_sub_v2 : Term_ → Symbol_ → Term_ → Term_ → Prop

-- if x = y then y [ x := N ] = N
| var_same
  (y : Symbol_)
  (x : Symbol_)
  (N : Term_) :
  x = y →
  is_sub_v2 (var_ y) x N N

-- if x ≠ y then y [ x := N ] = y
| var_diff
  (y : Symbol_)
  (x : Symbol_)
  (N : Term_) :
  ¬ x = y →
  is_sub_v2 (var_ y) x N (var_ y)

-- (P Q) [ x := N ] = (P [ x := N ] Q [ x := N ])
| app
  (P : Term_)
  (Q : Term_)
  (x : Symbol_)
  (N : Term_)
  (P' : Term_)
  (Q' : Term_) :
  is_sub_v2 P x N P' →
  is_sub_v2 Q x N Q' →
  is_sub_v2 (app_ P Q) x N (app_ P' Q')

-- if x = y then ( λ y . P ) [ x := N ] = ( λ y . P )
| abs_1
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_) :
  x = y →
  is_sub_v2 (abs_ y P) x N (abs_ y P)

| abs_2
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_) :
  ¬ x = y →
  x ∉ P.free_var_set →
  is_sub_v2 (abs_ y P) x N (abs_ y P)

| abs_3
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_)
  (P' : Term_) :
  ¬ x = y →
  y ∉ N.free_var_set →
  is_sub_v2 P x N P' →
  is_sub_v2 (abs_ y P) x N (abs_ y P')


-------------------------------------------------------------------------------


-- [1]

/--
  is_sub_v3 M x N L := True if and only if L is the result of replacing each free occurrence of x in M by N and no free occurrence of a variable in N becomes a bound occurrence in L.
  M [ x := N ] = L
-/
inductive is_sub_v3 : Term_ → Symbol_ → Term_ → Term_ → Prop

-- if x = y then y [ x := N ] = N
| var_same
  (y : Symbol_)
  (x : Symbol_)
  (N : Term_) :
  x = y →
  is_sub_v3 (var_ y) x N N

-- if x ≠ y then y [ x := N ] = y
| var_diff
  (y : Symbol_)
  (x : Symbol_)
  (N : Term_) :
  ¬ x = y →
  is_sub_v3 (var_ y) x N (var_ y)

-- (P Q) [ x := N ] = (P [ x := N ] Q [ x := N ])
| app
  (P : Term_)
  (Q : Term_)
  (x : Symbol_)
  (N : Term_)
  (P' : Term_)
  (Q' : Term_) :
  is_sub_v3 P x N P' →
  is_sub_v3 Q x N Q' →
  is_sub_v3 (app_ P Q) x N (app_ P' Q')

-- if x = y then ( λ y . P ) [ x := N ] = ( λ y . P )
| abs_1
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_) :
  x = y →
  is_sub_v3 (abs_ y P) x N (abs_ y P)

| abs_2
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_)
  (P' : Term_) :
  ¬ x = y →
  x ∉ P.free_var_set →
  is_sub_v3 P x N P' →
  is_sub_v3 (abs_ y P) x N (abs_ y P')

| abs_3
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_)
  (P' : Term_) :
  ¬ x = y →
  y ∉ N.free_var_set →
  is_sub_v3 P x N P' →
  is_sub_v3 (abs_ y P) x N (abs_ y P')


-------------------------------------------------------------------------------


-- [2]

inductive is_sub_v4 : Term_ → Symbol_ → Term_ → Term_ → Prop

| var_same
  (y : Symbol_)
  (x : Symbol_)
  (N : Term_) :
  x = y →
  is_sub_v4 (var_ y) x N N

| var_diff
  (y : Symbol_)
  (x : Symbol_)
  (N : Term_) :
  ¬ x = y →
  is_sub_v4 (var_ y) x N (var_ y)

| app
  (P : Term_)
  (Q : Term_)
  (x : Symbol_)
  (N : Term_)
  (P' : Term_)
  (Q' : Term_) :
  is_sub_v4 P x N P' →
  is_sub_v4 Q x N Q' →
  is_sub_v4 (app_ P Q) x N (app_ P' Q')

| abs_1
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_) :
  x = y →
  is_sub_v4 (abs_ y P) x N (abs_ y P)

| abs_2
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_)
  (P' : Term_) :
  ¬ x = y →
  x ∉ P.free_var_set →
  is_sub_v4 P x N P' →
  is_sub_v4 (abs_ y P) x N (abs_ y P')

| abs_3
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_)
  (P' : Term_) :
  ¬ x = y →
  y ∉ N.free_var_set →
  is_sub_v4 P x N P' →
  is_sub_v4 (abs_ y P) x N (abs_ y P')

| alpha
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_)
  (P' : Term_)
  (z : Symbol_) :
  z ∉ N.free_var_set →
  are_alpha_equiv_v2 (abs_ y P) (abs_ z (replace_free y (var_ z) P)) →
  is_sub_v4 (replace_free y (var_ z) P) x N P' →
  is_sub_v4 (abs_ y P) x N (abs_ z P')


-------------------------------------------------------------------------------


-- [1]
lemma lemma_1_2_5_i
  (M : Term_)
  (x : Symbol_)
  (N : Term_)
  (h1 : x ∉ M.free_var_set) :
  is_sub_v3 M x N M :=
  by
    induction M
    case var_ x_ =>
      unfold Term_.free_var_set at h1
      simp at h1
      exact is_sub_v3.var_diff x_ x N h1
    case app_ P_ Q_ ih_1 ih_2 =>
      unfold Term_.free_var_set at h1
      simp at h1
      obtain ⟨h1_left, h1_right⟩ := h1
      specialize ih_1 h1_left
      specialize ih_2 h1_right
      exact is_sub_v3.app P_ Q_ x N P_ Q_ ih_1 ih_2
    case abs_ x_ P_ ih =>
      by_cases c1 : x = x_
      · apply is_sub_v3.abs_1 x_ P_ x N c1
      · apply is_sub_v3.abs_2
        · exact c1
        · unfold free_var_set at h1
          simp at h1
          tauto
        · apply ih
          unfold Term_.free_var_set at h1
          simp at h1
          intro contra
          apply c1
          exact h1 contra


example
  (M : Term_)
  (x : Symbol_)
  (N : Term_)
  (L : Term_)
  (h1 : is_sub_v3 M x N L) :
  replace_free x N M = L :=
  by
    induction h1
    case var_same y_ x_ N_ ih =>
      unfold replace_free
      split_ifs
      rfl
    case var_diff y_ x_ N_ ih =>
      unfold replace_free
      split_ifs
      rfl
    case app P_ Q_ x_ N_ P'_ Q'_ ih_1 ih_2 ih_3 ih_4 =>
      unfold replace_free
      rw [ih_3]
      rw [ih_4]
    case abs_1 y_ P_ x_ N_ ih =>
      unfold replace_free
      split_ifs
      rfl
    case abs_2 y_ P_ x_ N_ P'_ ih_1 ih_2 ih_3 ih_4 =>
      unfold replace_free
      split_ifs
      rw [ih_4]
    case abs_3 y_ P_ x_ N_ P'_ ih_1 ih_2 ih_3 ih_4 =>
      unfold replace_free
      split_ifs
      rw [ih_4]


example
  (M : Term_)
  (x : Symbol_)
  (N : Term_)
  (h1 : ∃ (L : Term_), is_sub_v3 M x N L) :
  sub_is_def_v3 M x N :=
  by
    obtain ⟨e3, h1⟩ := h1
    induction h1
    case var_same y_ x_ _ _ =>
      apply sub_is_def_v3.var
    case var_diff y_ x_ N_ _ =>
      apply sub_is_def_v3.var
    case app P_ Q_ x_ N_ _ _ _ _ ih_3 ih_4 =>
      apply sub_is_def_v3.app; exact ih_3; exact ih_4
    case abs_1 y_ P_ x_ N_ ih =>
      apply sub_is_def_v3.abs_1; exact ih
    case abs_2 y_ P_ x_ N_ _ ih_1 ih_2 _ _ =>
      apply sub_is_def_v3.abs_2; exact ih_1; exact ih_2
    case abs_3 y_ P_ x_ N_ _ ih_1 ih_2 _ ih_4 =>
      apply sub_is_def_v3.abs_3; exact ih_1; exact ih_2; exact ih_4


example
  (M : Term_)
  (x : Symbol_)
  (N : Term_)
  (h1 : sub_is_def_v3 M x N) :
  is_sub_v3 M x N (replace_free x N M) :=
  by
    induction h1
    case var y_ x_ N_ =>
      unfold replace_free
      split_ifs
      case pos c1 =>
        apply is_sub_v3.var_same; exact c1
      case neg c1 =>
        apply is_sub_v3.var_diff; exact c1
    case app P_ Q_ x_ N_ ih_1 _ ih_3 ih_4 =>
      apply is_sub_v3.app; exact ih_3; exact ih_4
    case abs_1 y_ P_ x_ N_ ih_1 =>
      unfold replace_free
      split_ifs
      apply is_sub_v3.abs_1; exact ih_1
    case abs_2 y_ P_ x_ N_ ih_1 ih_2 =>
      have s1 : replace_free x_ N_ (abs_ y_ P_) = abs_ y_ P_ :=
      by
        apply replace_free_not_mem
        unfold free_var_set
        simp
        tauto
      rw [s1]
      apply lemma_1_2_5_i
      unfold free_var_set
      simp
      tauto
    case abs_3 y_ P_ x_ N_ ih_1 ih_2 ih_3 ih_4 =>
      unfold replace_free
      split_ifs
      apply is_sub_v3.abs_3
      · exact ih_1
      · exact ih_2
      · exact ih_4


-- [1]
lemma lemma_1_2_5_iii
  (M : Term_)
  (x : Symbol_) :
  is_sub_v3 M x (var_ x) M :=
  by
    induction M
    case var_ x_ =>
      by_cases c1 : x = x_
      case pos =>
        rw [c1]
        apply is_sub_v3.var_same
        rfl
      case neg =>
        apply is_sub_v3.var_diff
        exact c1
    case app_ P_ Q_ ih_1 ih_2 =>
      apply is_sub_v3.app
      · exact ih_1
      · exact ih_2
    case abs_ x_ P_ ih =>
      by_cases c1 : x = x_
      case pos =>
        apply is_sub_v3.abs_1
        exact c1
      case neg =>
        apply is_sub_v3.abs_3
        · exact c1
        · unfold free_var_set
          simp
          intro contra
          apply c1
          rw [contra]
        · exact ih


-------------------------------------------------------------------------------


lemma is_sub_v1_imp_is_sub_v2
  (M : Term_)
  (x : Symbol_)
  (N : Term_)
  (L : Term_)
  (h1 : is_sub_v1 M x N L) :
  is_sub_v2 M x N L :=
  by
    induction h1
    case var_same y_ x_ N_ ih =>
      apply is_sub_v2.var_same
      exact ih
    case var_diff y_ x_ N_ ih =>
      apply is_sub_v2.var_diff
      exact ih
    case app P_ Q_ x_ N_ P'_ Q'_ ih_1 ih_2 ih_3 ih_4 =>
      apply is_sub_v2.app
      · exact ih_3
      · exact ih_4
    case abs_1 y_ P_ x_ N_ ih =>
      unfold free_var_set at ih
      simp at ih
      by_cases c1 : x_ = y_
      case pos =>
        apply is_sub_v2.abs_1
        exact c1
      case neg =>
        apply is_sub_v2.abs_2
        · exact c1
        · tauto
    case abs_2 y_ P_ x_ N_ P'_ ih_1 ih_2 ih_3 ih_4 =>
      apply is_sub_v2.abs_3
      · exact ih_1
      · exact ih_2
      · exact ih_4


lemma is_sub_v2_imp_is_sub_v1
  (M : Term_)
  (x : Symbol_)
  (N : Term_)
  (L : Term_)
  (h1 : is_sub_v2 M x N L) :
  is_sub_v1 M x N L :=
  by
    induction h1
    case var_same y_ x_ N_ ih =>
      apply is_sub_v1.var_same
      exact ih
    case var_diff y_ x_ N_ ih =>
      apply is_sub_v1.var_diff
      exact ih
    case app P_ Q_ x_ N_ P'_ Q'_ ih_1 ih_2 ih_3 ih_4 =>
      apply is_sub_v1.app
      · exact ih_3
      · exact ih_4
    case abs_1 y_ P_ x_ N_ ih =>
      apply is_sub_v1.abs_1
      unfold free_var_set
      simp
      intro a1
      exact ih
    case abs_2 y_ P_ x_ N_ ih_1 ih_2 =>
      apply is_sub_v1.abs_1
      unfold free_var_set
      simp
      intro contra
      contradiction
    case abs_3 y_ P_ x_ N_ P'_ ih_1 ih_2 ih_3 ih_4 =>
      apply is_sub_v1.abs_2
      · exact ih_1
      · exact ih_2
      · exact ih_4


lemma is_sub_v1_iff_is_sub_v2
  (M : Term_)
  (x : Symbol_)
  (N : Term_)
  (L : Term_) :
  is_sub_v1 M x N L ↔ is_sub_v2 M x N L :=
  by
    constructor
    · apply is_sub_v1_imp_is_sub_v2
    · apply is_sub_v2_imp_is_sub_v1


-------------------------------------------------------------------------------


lemma is_sub_v2_imp_is_sub_v3
  (M : Term_)
  (x : Symbol_)
  (N : Term_)
  (L : Term_)
  (h1 : is_sub_v2 M x N L) :
  is_sub_v3 M x N L :=
  by
    induction h1
    case var_same y_ x_ N_ ih =>
      apply is_sub_v3.var_same
      exact ih
    case var_diff y_ x_ N_ ih =>
      apply is_sub_v3.var_diff
      exact ih
    case app P_ Q_ x_ N_ P'_ Q'_ ih_1 ih_2 ih_3 ih_4 =>
      apply is_sub_v3.app
      · exact ih_3
      · exact ih_4
    case abs_1 y_ P_ x_ N_ ih_1 =>
      apply is_sub_v3.abs_1
      exact ih_1
    case abs_2 y_ P_ x_ N_ ih_1 ih_2 =>
      apply lemma_1_2_5_i
      unfold free_var_set
      simp
      intro
      contradiction
    case abs_3 y_ P_ x_ N_ P'_ ih_1 ih_2 ih_3 ih_4 =>
      apply is_sub_v3.abs_3
      · exact ih_1
      · exact ih_2
      · exact ih_4


theorem extracted_1
  (M : Term_)
  (x : Symbol_)
  (N : Term_)
  (L : Term_)
  (h1: x ∉ M.free_var_set)
  (h2 : is_sub_v2 M x N L) :
  M = L :=
  by
    induction h2
    case var_same y_ x_ N_ ih =>
      unfold free_var_set at h1
      simp at h1
      contradiction
    case var_diff y_ x_ N_ ih =>
      rfl
    case app P_ Q_ x_ N_ P'_ Q'_ ih_1 ih_2 ih_3 ih_4 =>
      unfold free_var_set at h1
      simp at h1
      obtain ⟨h1_left, h1_right⟩ := h1
      specialize ih_3 h1_left
      specialize ih_4 h1_right
      rw [ih_3]
      rw [ih_4]
    case abs_1 y_ P_ x_ N_ ih_1 =>
      rfl
    case abs_2 y_ P_ x_ N_ ih_1 ih_2 =>
      rfl
    case abs_3 y_ P_ x_ N_ P'_ ih_1 ih_2 ih_3 ih_4 =>
      unfold free_var_set at h1
      simp at h1
      have s1 : P_ = P'_ := by tauto
      rw [s1]


lemma is_sub_v3_imp_is_sub_v2
  (M : Term_)
  (x : Symbol_)
  (N : Term_)
  (L : Term_)
  (h1 : is_sub_v3 M x N L) :
  is_sub_v2 M x N L :=
  by
    induction h1
    case var_same y_ x_ N_ ih =>
      apply is_sub_v2.var_same
      exact ih
    case var_diff y_ x_ N_ ih =>
      apply is_sub_v2.var_diff
      exact ih
    case app P_ Q_ x_ N_ P'_ Q'_ ih_1 ih_2 ih_3 ih_4 =>
      apply is_sub_v2.app
      · exact ih_3
      · exact ih_4
    case abs_1 y_ P_ x_ N_ ih =>
      apply is_sub_v2.abs_1
      exact ih
    case abs_2 y_ P_ x_ N_ P'_ ih_1 ih_2 ih_3 ih_4 =>
      have s1 : x_ ∉ (abs_ y_ P_).free_var_set :=
      by
        unfold free_var_set
        simp
        intro contra
        contradiction
      have s2 : P_ = P'_ :=
      by
        apply extracted_1 P_ x_ N_ P'_ ih_2 ih_4
      subst s2
      apply is_sub_v2.abs_2
      · exact ih_1
      · exact ih_2
    case abs_3 y_ P_ x_ N_ P'_ ih_1 ih_2 ih_3 ih_4 =>
      apply is_sub_v2.abs_3
      · exact ih_1
      · exact ih_2
      · exact ih_4


lemma is_sub_v2_iff_is_sub_v3
  (M : Term_)
  (x : Symbol_)
  (N : Term_)
  (L : Term_) :
  is_sub_v2 M x N L ↔ is_sub_v3 M x N L :=
  by
    constructor
    · apply is_sub_v2_imp_is_sub_v3
    · apply is_sub_v3_imp_is_sub_v2


-------------------------------------------------------------------------------
