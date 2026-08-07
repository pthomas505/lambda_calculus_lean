import LambdaCalculusLean.NV.UTLC.Sub.Alpha
import LambdaCalculusLean.NV.UTLC.Sub.SubIsDef


set_option linter.style.emptyLine false
set_option linter.style.docString false
set_option linter.style.longLine false


inductive is_sub_v1 : Term_ → String → Term_ → Term_ → Prop

-- if x = y then y [ x := N ] = N
| var_same
  (y : String)
  (x : String)
  (N : Term_) :
  x = y →
  is_sub_v1 (Term_.Var y) x N N

-- if x ≠ y then y [ x := N ] = y
| var_diff
  (y : String)
  (x : String)
  (N : Term_) :
  ¬ x = y →
  is_sub_v1 (Term_.Var y) x N (Term_.Var y)

-- (P Q) [ x := N ] = (P [ x := N ] Q [ x := N ])
| app
  (P : Term_)
  (Q : Term_)
  (x : String)
  (N : Term_)
  (P' : Term_)
  (Q' : Term_) :
  is_sub_v1 P x N P' →
  is_sub_v1 Q x N Q' →
  is_sub_v1 (Term_.App P Q) x N (Term_.App P' Q')

| abs_1
  (y : String)
  (P : Term_)
  (x : String)
  (N : Term_) :
  ¬ is_free_in x (Term_.Abs y P) →
  is_sub_v1 (Term_.Abs y P) x N (Term_.Abs y P)

| abs_2
  (y : String)
  (P : Term_)
  (x : String)
  (N : Term_)
  (P' : Term_) :
  ¬ x = y →
  ¬ is_free_in y N →
  is_sub_v1 P x N P' →
  is_sub_v1 (Term_.Abs y P) x N (Term_.Abs y P')


/--
is_sub_v1_alt x N M L := x -> N in M = L
-/
inductive is_sub_v1_alt : String → Term_ → Term_ → Term_ → Prop

-- if x = y then y [ x := N ] = N
| var_same
  (x : String)
  (N : Term_)
  (y : String) :
  x = y →
  is_sub_v1_alt x N (Term_.Var y) N

-- if x ≠ y then y [ x := N ] = y
| var_diff
  (x : String)
  (N : Term_)
  (y : String) :
  ¬ x = y →
  is_sub_v1_alt x N (Term_.Var y) (Term_.Var y)

-- (P Q) [ x := N ] = (P [ x := N ] Q [ x := N ])
| app
  (x : String)
  (N : Term_)
  (P : Term_)
  (Q : Term_)
  (P' : Term_)
  (Q' : Term_) :
  is_sub_v1_alt x N P P' →
  is_sub_v1_alt x N Q Q' →
  is_sub_v1_alt x N (Term_.App P Q) (Term_.App P' Q')

| abs_1
  (x : String)
  (N : Term_)
  (y : String)
  (P : Term_) :
  ¬ is_free_in x (Term_.Abs y P) →
  is_sub_v1_alt x N (Term_.Abs y P) (Term_.Abs y P)

| abs_2
  (x : String)
  (N : Term_)
  (y : String)
  (P : Term_)
  (P' : Term_) :
  ¬ x = y →
  ¬ is_free_in y N →
  is_sub_v1_alt x N P P' →
  is_sub_v1_alt x N (Term_.Abs y P) (Term_.Abs y P')


example
  (M : Term_)
  (x : String)
  (N : Term_)
  (L : Term_)
  (h1 : is_sub_v1 M x N L) :
  is_sub_v1_alt x N M L :=
  by
  induction h1
  case var_same y_ x_ N_ ih =>
    apply is_sub_v1_alt.var_same
    exact ih
  case var_diff y_ x_ N_ ih =>
    apply is_sub_v1_alt.var_diff
    exact ih
  case app P_ Q_ x_ N_ P'_ Q'_ ih_1 ih_2 ih_3 ih_4 =>
    apply is_sub_v1_alt.app
    · exact ih_3
    · exact ih_4
  case abs_1 y_ P_ x_ N_ ih =>
    apply is_sub_v1_alt.abs_1
    exact ih
  case abs_2 y_ P_ x_ N_ P'_ ih_1 ih_2 ih_3 ih_4 =>
    apply is_sub_v1_alt.abs_2
    · exact ih_1
    · exact ih_2
    · exact ih_4


example
  (x : String)
  (N : Term_)
  (M : Term_)
  (L : Term_)
  (h1 : is_sub_v1_alt x N M L) :
  is_sub_v1 M x N L :=
  by
  induction h1
  case var_same y ih =>
    apply is_sub_v1.var_same
    exact ih
  case var_diff y ih =>
    apply is_sub_v1.var_diff
    exact ih
  case app P Q P' Q' ih_1 ih_2 ih_3 ih_4 =>
    apply is_sub_v1.app
    · exact ih_3
    · exact ih_4
  case abs_1 y P ih =>
    apply is_sub_v1.abs_1
    exact ih
  case abs_2 y P P' ih_1 ih_2 ih_3 ih_4 =>
    apply is_sub_v1.abs_2
    · exact ih_1
    · exact ih_2
    · exact ih_4


-------------------------------------------------------------------------------


inductive is_sub_v2 : Term_ → String → Term_ → Term_ → Prop

-- if x = y then y [ x := N ] = N
| var_same
  (y : String)
  (x : String)
  (N : Term_) :
  x = y →
  is_sub_v2 (Term_.Var y) x N N

-- if x ≠ y then y [ x := N ] = y
| var_diff
  (y : String)
  (x : String)
  (N : Term_) :
  ¬ x = y →
  is_sub_v2 (Term_.Var y) x N (Term_.Var y)

-- (P Q) [ x := N ] = (P [ x := N ] Q [ x := N ])
| app
  (P : Term_)
  (Q : Term_)
  (x : String)
  (N : Term_)
  (P' : Term_)
  (Q' : Term_) :
  is_sub_v2 P x N P' →
  is_sub_v2 Q x N Q' →
  is_sub_v2 (Term_.App P Q) x N (Term_.App P' Q')

-- if x = y then ( λ y . P ) [ x := N ] = ( λ y . P )
| abs_1
  (y : String)
  (P : Term_)
  (x : String)
  (N : Term_) :
  x = y →
  is_sub_v2 (Term_.Abs y P) x N (Term_.Abs y P)

| abs_2
  (y : String)
  (P : Term_)
  (x : String)
  (N : Term_) :
  ¬ x = y →
  ¬ is_free_in x P →
  is_sub_v2 (Term_.Abs y P) x N (Term_.Abs y P)

| abs_3
  (y : String)
  (P : Term_)
  (x : String)
  (N : Term_)
  (P' : Term_) :
  ¬ x = y →
  ¬ is_free_in y N →
  is_sub_v2 P x N P' →
  is_sub_v2 (Term_.Abs y P) x N (Term_.Abs y P')


inductive is_sub_v2_alt : String → Term_ → Term_ → Term_ → Prop

-- if x = y then y [ x := N ] = N
| var_same
  (x : String)
  (N : Term_)
  (y : String) :
  x = y →
  is_sub_v2_alt x N (Term_.Var y) N

-- if x ≠ y then y [ x := N ] = y
| var_diff
  (x : String)
  (N : Term_)
  (y : String) :
  ¬ x = y →
  is_sub_v2_alt x N (Term_.Var y) (Term_.Var y)

-- (P Q) [ x := N ] = (P [ x := N ] Q [ x := N ])
| app
  (x : String)
  (N : Term_)
  (P : Term_)
  (Q : Term_)
  (P' : Term_)
  (Q' : Term_) :
  is_sub_v2_alt x N P P' →
  is_sub_v2_alt x N Q Q' →
  is_sub_v2_alt x N (Term_.App P Q) (Term_.App P' Q')

-- if x = y then ( λ y . P ) [ x := N ] = ( λ y . P )
| abs_1
  (x : String)
  (N : Term_)
  (y : String)
  (P : Term_) :
  x = y →
  is_sub_v2_alt x N (Term_.Abs y P) (Term_.Abs y P)

| abs_2
  (x : String)
  (N : Term_)
  (y : String)
  (P : Term_) :
  ¬ x = y →
  ¬ is_free_in x P →
  is_sub_v2_alt x N (Term_.Abs y P) (Term_.Abs y P)

| abs_3
  (x : String)
  (N : Term_)
  (y : String)
  (P : Term_)
  (P' : Term_) :
  ¬ x = y →
  ¬ is_free_in y N →
  is_sub_v2_alt x N P P' →
  is_sub_v2_alt x N (Term_.Abs y P) (Term_.Abs y P')


example
  (M : Term_)
  (x : String)
  (N : Term_)
  (L : Term_)
  (h1 : is_sub_v2 M x N L) :
  is_sub_v2_alt x N M L :=
  by
  induction h1
  case var_same y_ x_ N_ ih =>
    apply is_sub_v2_alt.var_same
    exact ih
  case var_diff y_ x_ N_ ih =>
    apply is_sub_v2_alt.var_diff
    exact ih
  case app P_ Q_ x_ N_ P'_ Q'_ ih_1 ih_2 ih_3 ih_4 =>
    apply is_sub_v2_alt.app
    · exact ih_3
    · exact ih_4
  case abs_1 y_ P_ x_ N_ ih =>
    apply is_sub_v2_alt.abs_1
    exact ih
  case abs_2 y_ P_ x_ N_ ih_1 ih_2 =>
    apply is_sub_v2_alt.abs_2
    · exact ih_1
    · exact ih_2
  case abs_3 y_ P_ x_ N_ P'_ ih_1 ih_2 ih_3 ih_4 =>
    apply is_sub_v2_alt.abs_3
    · exact ih_1
    · exact ih_2
    · exact ih_4


example
  (x : String)
  (N : Term_)
  (M : Term_)
  (L : Term_)
  (h1 : is_sub_v2_alt x N M L) :
  is_sub_v2 M x N L :=
  by
  induction h1
  case var_same y ih =>
    apply is_sub_v2.var_same
    exact ih
  case var_diff y ih =>
    apply is_sub_v2.var_diff
    exact ih
  case app P Q P' Q' ih_1 ih_2 ih_3 ih_4 =>
    apply is_sub_v2.app
    · exact ih_3
    · exact ih_4
  case abs_1 y P ih =>
    apply is_sub_v2.abs_1
    exact ih
  case abs_2 y P ih_1 ih_2 =>
    apply is_sub_v2.abs_2
    · exact ih_1
    · exact ih_2
  case abs_3 y P P' ih_1 ih_2 ih_3 ih_4 =>
    apply is_sub_v2.abs_3
    · exact ih_1
    · exact ih_2
    · exact ih_4


-------------------------------------------------------------------------------


-- [1]

/--
  is_sub_v3 M x N L := True if and only if L is the result of replacing each free occurrence of x in M by N and no free occurrence of a variable in N becomes a bound occurrence in L.
  M [ x := N ] = L
-/
inductive is_sub_v3 : Term_ → String → Term_ → Term_ → Prop

-- if x = y then y [ x := N ] = N
| var_same
  (y : String)
  (x : String)
  (N : Term_) :
  x = y →
  is_sub_v3 (Term_.Var y) x N N

-- if x ≠ y then y [ x := N ] = y
| var_diff
  (y : String)
  (x : String)
  (N : Term_) :
  ¬ x = y →
  is_sub_v3 (Term_.Var y) x N (Term_.Var y)

-- (P Q) [ x := N ] = (P [ x := N ] Q [ x := N ])
| app
  (P : Term_)
  (Q : Term_)
  (x : String)
  (N : Term_)
  (P' : Term_)
  (Q' : Term_) :
  is_sub_v3 P x N P' →
  is_sub_v3 Q x N Q' →
  is_sub_v3 (Term_.App P Q) x N (Term_.App P' Q')

-- if x = y then ( λ y . P ) [ x := N ] = ( λ y . P )
| abs_1
  (y : String)
  (P : Term_)
  (x : String)
  (N : Term_) :
  x = y →
  is_sub_v3 (Term_.Abs y P) x N (Term_.Abs y P)

| abs_2
  (y : String)
  (P : Term_)
  (x : String)
  (N : Term_)
  (P' : Term_) :
  ¬ x = y →
  ¬ is_free_in x P →
  is_sub_v3 P x N P' →
  is_sub_v3 (Term_.Abs y P) x N (Term_.Abs y P')

| abs_3
  (y : String)
  (P : Term_)
  (x : String)
  (N : Term_)
  (P' : Term_) :
  ¬ x = y →
  ¬ is_free_in y N →
  is_sub_v3 P x N P' →
  is_sub_v3 (Term_.Abs y P) x N (Term_.Abs y P')


inductive is_sub_v3_alt : String → Term_ → Term_ → Term_ → Prop

-- if x = y then y [ x := N ] = N
| var_same
  (x : String)
  (N : Term_)
  (y : String) :
  x = y →
  is_sub_v3_alt x N (Term_.Var y) N

-- if x ≠ y then y [ x := N ] = y
| var_diff
  (x : String)
  (N : Term_)
  (y : String) :
  ¬ x = y →
  is_sub_v3_alt x N (Term_.Var y) (Term_.Var y)

-- (P Q) [ x := N ] = (P [ x := N ] Q [ x := N ])
| app
  (x : String)
  (N : Term_)
  (P : Term_)
  (Q : Term_)
  (P' : Term_)
  (Q' : Term_) :
  is_sub_v3_alt x N P P' →
  is_sub_v3_alt x N Q Q' →
  is_sub_v3_alt x N (Term_.App P Q) (Term_.App P' Q')

-- if x = y then ( λ y . P ) [ x := N ] = ( λ y . P )
| abs_1
  (x : String)
  (N : Term_)
  (y : String)
  (P : Term_) :
  x = y →
  is_sub_v3_alt x N (Term_.Abs y P) (Term_.Abs y P)

| abs_2
  (x : String)
  (N : Term_)
  (y : String)
  (P : Term_)
  (P' : Term_) :
  ¬ x = y →
  ¬ is_free_in x P →
  is_sub_v3_alt x N P P' →
  is_sub_v3_alt x N (Term_.Abs y P) (Term_.Abs y P')

| abs_3
  (x : String)
  (N : Term_)
  (y : String)
  (P : Term_)
  (P' : Term_) :
  ¬ x = y →
  ¬ is_free_in y N →
  is_sub_v3_alt x N P P' →
  is_sub_v3_alt x N (Term_.Abs y P) (Term_.Abs y P')


example
  (M : Term_)
  (x : String)
  (N : Term_)
  (L : Term_)
  (h1 : is_sub_v3 M x N L) :
  is_sub_v3_alt x N M L :=
  by
  induction h1
  case var_same y_ x_ N_ ih =>
    apply is_sub_v3_alt.var_same
    exact ih
  case var_diff y_ x_ N_ ih =>
    apply is_sub_v3_alt.var_diff
    exact ih
  case app P_ Q_ x_ N_ P'_ Q'_ ih_1 ih_2 ih_3 ih_4 =>
    apply is_sub_v3_alt.app
    · exact ih_3
    · exact ih_4
  case abs_1 y_ P_ x_ N_ ih =>
    apply is_sub_v3_alt.abs_1
    exact ih
  case abs_2 y_ P_ x_ N_ P'_ ih_1 ih_2 ih_3 ih_4 =>
    apply is_sub_v3_alt.abs_2
    · exact ih_1
    · exact ih_2
    · exact ih_4
  case abs_3 y_ P_ x_ N_ P'_ ih_1 ih_2 ih_3 ih_4 =>
    apply is_sub_v3_alt.abs_3
    · exact ih_1
    · exact ih_2
    · exact ih_4


example
  (x : String)
  (N : Term_)
  (M : Term_)
  (L : Term_)
  (h1 : is_sub_v3_alt x N M L) :
  is_sub_v3 M x N L :=
  by
  induction h1
  case var_same y ih =>
    apply is_sub_v3.var_same
    exact ih
  case var_diff y ih =>
    apply is_sub_v3.var_diff
    exact ih
  case app P Q P' Q' ih_1 ih_2 ih_3 ih_4 =>
    apply is_sub_v3.app
    · exact ih_3
    · exact ih_4
  case abs_1 y P ih =>
    apply is_sub_v3.abs_1
    exact ih
  case abs_2 y P P' ih_1 ih_2 ih_3 ih_4 =>
    apply is_sub_v3.abs_2
    · exact ih_1
    · exact ih_2
    · exact ih_4
  case abs_3 y P P' ih_1 ih_2 ih_3 ih_4 =>
    apply is_sub_v3.abs_3
    · exact ih_1
    · exact ih_2
    · exact ih_4


-------------------------------------------------------------------------------


-- [2]

inductive is_sub_v4 : Term_ → String → Term_ → Term_ → Prop

| var_same
  (y : String)
  (x : String)
  (N : Term_) :
  x = y →
  is_sub_v4 (Term_.Var y) x N N

| var_diff
  (y : String)
  (x : String)
  (N : Term_) :
  ¬ x = y →
  is_sub_v4 (Term_.Var y) x N (Term_.Var y)

| app
  (P : Term_)
  (Q : Term_)
  (x : String)
  (N : Term_)
  (P' : Term_)
  (Q' : Term_) :
  is_sub_v4 P x N P' →
  is_sub_v4 Q x N Q' →
  is_sub_v4 (Term_.App P Q) x N (Term_.App P' Q')

| abs_1
  (y : String)
  (P : Term_)
  (x : String)
  (N : Term_) :
  x = y →
  is_sub_v4 (Term_.Abs y P) x N (Term_.Abs y P)

| abs_2
  (y : String)
  (P : Term_)
  (x : String)
  (N : Term_)
  (P' : Term_) :
  ¬ x = y →
  ¬ is_free_in x P →
  is_sub_v4 P x N P' →
  is_sub_v4 (Term_.Abs y P) x N (Term_.Abs y P')

| abs_3
  (y : String)
  (P : Term_)
  (x : String)
  (N : Term_)
  (P' : Term_) :
  ¬ x = y →
  ¬ is_free_in y N →
  is_sub_v4 P x N P' →
  is_sub_v4 (Term_.Abs y P) x N (Term_.Abs y P')

| alpha
  (y : String)
  (P : Term_)
  (x : String)
  (N : Term_)
  (P' : Term_)
  (z : String) :
  ¬ is_free_in z N →
  are_alpha_equiv_v2 (Term_.Abs y P) (Term_.Abs z (replace_free y (Term_.Var z) P)) →
  is_sub_v4 (replace_free y (Term_.Var z) P) x N P' →
  is_sub_v4 (Term_.Abs y P) x N (Term_.Abs z P')


-------------------------------------------------------------------------------


theorem not_is_free_in_is_sub
  (x : String)
  (N : Term_)
  (M : Term_)
  (h1 : ¬ is_free_in x M) :
  is_sub_v3_alt x N M M :=
  by
    induction M
    case Var v =>
      apply is_sub_v3_alt.var_diff
      exact h1
    case App P Q ih_1 ih_2 =>
      unfold is_free_in at h1
      rewrite [not_or] at h1
      obtain ⟨h1_left, h1_right⟩ := h1

      apply is_sub_v3_alt.app
      · exact ih_1 h1_left
      · exact ih_2 h1_right
    case Abs v P ih =>
      unfold is_free_in at h1
      rewrite [not_and] at h1

      by_cases c1 : x = v
      · apply is_sub_v3_alt.abs_1
        exact c1
      · apply is_sub_v3_alt.abs_2
        · exact c1
        · apply h1
          exact c1
        · apply ih
          apply h1
          exact c1


-- ----------------------------------------------------------------------------


theorem is_sub_var_eq
  (x : String)
  (M : Term_) :
  is_sub_v3_alt x (Term_.Var x) M M :=
  by
    induction M
    case Var v =>
      by_cases c1 : x = v
      · rewrite [c1]
        apply is_sub_v3_alt.var_same
        apply Eq.refl
      · apply is_sub_v3_alt.var_diff
        exact c1
    case App P Q ih_1 ih_2 =>
      apply is_sub_v3_alt.app
      · exact ih_1
      · exact ih_2
    case Abs v P ih =>
      by_cases c1 : x = v
      · apply is_sub_v3_alt.abs_1
        exact c1
      · apply is_sub_v3_alt.abs_3
        · exact c1
        · unfold is_free_in
          rewrite [neq_comm]
          exact c1
        · exact ih


-- ----------------------------------------------------------------------------


example
  (x : String)
  (N : Term_)
  (M : Term_)
  (L : Term_)
  (h1 : is_sub_v3_alt x N M L) :
  replace_free x N M = L :=
  by
    induction h1
    case var_same y ih =>
      unfold replace_free
      split
      case isTrue c1 =>
        apply Eq.refl
      case isFalse c1 =>
        contradiction
    case var_diff y ih =>
      unfold replace_free
      split
      case isTrue c1 =>
        contradiction
      case isFalse c1 =>
        apply Eq.refl
    case app P Q P' Q' ih_1 ih_2 ih_3 ih_4 =>
      unfold replace_free
      rewrite [ih_3]
      rewrite [ih_4]
      apply Eq.refl
    case abs_1 y P ih =>
      unfold replace_free
      split
      case isTrue c1 =>
        apply Eq.refl
      case isFalse c1 =>
        contradiction
    case abs_2 y P P' ih_1 ih_2 ih_3 ih_4 =>
      unfold replace_free
      split
      case isTrue c1 =>
        contradiction
      case isFalse c1 =>
        rewrite [ih_4]
        apply Eq.refl
    case abs_3 y P P' ih_1 ih_2 ih_3 ih_4 =>
      unfold replace_free
      split
      case isTrue c1 =>
        contradiction
      case isFalse c1 =>
        rewrite [ih_4]
        apply Eq.refl


example
  (x : String)
  (N : Term_)
  (M : Term_)
  (L : Term_)
  (h1 : is_sub_v3_alt x N M L) :
  sub_is_def_v3_alt x N M :=
  by
    induction h1
    case var_same y ih =>
      apply sub_is_def_v3_alt.var
    case var_diff y ih =>
      apply sub_is_def_v3_alt.var
    case app P Q P' Q' ih_1 ih_2 ih_3 ih_4 =>
      apply sub_is_def_v3_alt.app
      · exact ih_3
      · exact ih_4
    case abs_1 y P ih =>
      apply sub_is_def_v3_alt.abs_1
      exact ih
    case abs_2 y P P' ih_1 ih_2 ih_3 ih_4 =>
      apply sub_is_def_v3_alt.abs_2
      · exact ih_1
      · exact ih_2
    case abs_3 y P P' ih_1 ih_2 ih_3 ih_4 =>
      apply sub_is_def_v3_alt.abs_3
      · exact ih_1
      · exact ih_2
      · exact ih_4


example
  (x : String)
  (N : Term_)
  (M : Term_)
  (h1 : sub_is_def_v3_alt x N M) :
  is_sub_v3_alt x N M (replace_free x N M) :=
  by
    induction h1
    case var y =>
      unfold replace_free
      split
      case isTrue c1 =>
        apply is_sub_v3_alt.var_same
        exact c1
      case isFalse c1 =>
        apply is_sub_v3_alt.var_diff
        exact c1
    case app P Q ih_1 ih_2 ih_3 ih_4 =>
      apply is_sub_v3_alt.app
      · exact ih_3
      · exact ih_4
    case abs_1 y P ih =>
      unfold replace_free
      split
      case isTrue c1 =>
        apply is_sub_v3_alt.abs_1
        exact ih
      case isFalse c1 =>
        contradiction
    case abs_2 y P ih_1 ih_2 =>
      have s1 : replace_free x N (Term_.Abs y P) = Term_.Abs y P :=
      by
        apply not_is_free_in_replace_free
        unfold is_free_in
        rewrite [not_and]
        intro a1
        exact ih_2
      rewrite [s1]
      apply not_is_free_in_is_sub
      unfold is_free_in
      rewrite [not_and]
      intro a1
      exact ih_2
    case abs_3 y P ih_1 ih_2 ih_3 ih_4 =>
      unfold replace_free
      split
      case isTrue c1 =>
        contradiction
      case isFalse c1 =>
        apply is_sub_v3_alt.abs_3
        · exact ih_1
        · exact ih_2
        · exact ih_4


-------------------------------------------------------------------------------


theorem is_sub_v1_imp_is_sub_v2
  (x : String)
  (N : Term_)
  (M : Term_)
  (L : Term_)
  (h1 : is_sub_v1_alt x N M L) :
  is_sub_v2_alt x N M L :=
  by
    induction h1
    case var_same y ih =>
      apply is_sub_v2_alt.var_same
      exact ih
    case var_diff y ih =>
      apply is_sub_v2_alt.var_diff
      exact ih
    case app P Q P' Q' ih_1 ih_2 ih_3 ih_4 =>
      apply is_sub_v2_alt.app
      · exact ih_3
      · exact ih_4
    case abs_1 y P ih =>
      unfold is_free_in at ih
      rewrite [not_and] at ih

      by_cases c1 : x = y
      · apply is_sub_v2_alt.abs_1
        exact c1
      · apply is_sub_v2_alt.abs_2
        · exact c1
        · apply ih
          exact c1
    case abs_2 y P P' ih_1 ih_2 ih_3 ih_4 =>
      apply is_sub_v2_alt.abs_3
      · exact ih_1
      · exact ih_2
      · exact ih_4


theorem is_sub_v2_imp_is_sub_v1
  (x : String)
  (N : Term_)
  (M : Term_)
  (L : Term_)
  (h1 : is_sub_v2_alt x N M L) :
  is_sub_v1_alt x N M L :=
  by
    induction h1
    case var_same y ih =>
      apply is_sub_v1_alt.var_same
      exact ih
    case var_diff y ih =>
      apply is_sub_v1_alt.var_diff
      exact ih
    case app P Q P' Q' ih_1 ih_2 ih_3 ih_4 =>
      apply is_sub_v1_alt.app
      · exact ih_3
      · exact ih_4
    case abs_1 y P ih =>
      apply is_sub_v1_alt.abs_1
      unfold is_free_in
      rewrite [not_and]
      intro a1
      contradiction
    case abs_2 y P ih_1 ih_2 =>
      apply is_sub_v1_alt.abs_1
      unfold is_free_in
      rewrite [not_and]
      intro a1
      exact ih_2
    case abs_3 y P P' ih_1 ih_2 ih_3 ih_4 =>
      apply is_sub_v1_alt.abs_2
      · exact ih_1
      · exact ih_2
      · exact ih_4


theorem is_sub_v1_iff_is_sub_v2
  (x : String)
  (N : Term_)
  (M : Term_)
  (L : Term_) :
  is_sub_v1_alt x N M L ↔ is_sub_v2_alt x N M L :=
  by
    constructor
    · apply is_sub_v1_imp_is_sub_v2
    · apply is_sub_v2_imp_is_sub_v1


-------------------------------------------------------------------------------


theorem is_sub_v2_imp_is_sub_v3
  (x : String)
  (N : Term_)
  (M : Term_)
  (L : Term_)
  (h1 : is_sub_v2_alt x N M L) :
  is_sub_v3_alt x N M L :=
  by
    induction h1
    case var_same y ih =>
      apply is_sub_v3_alt.var_same
      exact ih
    case var_diff y ih =>
      apply is_sub_v3_alt.var_diff
      exact ih
    case app P Q P' Q' ih_1 ih_2 ih_3 ih_4 =>
      apply is_sub_v3_alt.app
      · exact ih_3
      · exact ih_4
    case abs_1 y P ih =>
      apply is_sub_v3_alt.abs_1
      exact ih
    case abs_2 y P ih_1 ih_2 =>
      apply not_is_free_in_is_sub
      unfold is_free_in
      rewrite [not_and]
      intro a1
      exact ih_2
    case abs_3 y P P' ih_1 ih_2 ih_3 ih_4 =>
      apply is_sub_v3_alt.abs_3
      · exact ih_1
      · exact ih_2
      · exact ih_4


theorem extracted_1
  (x : String)
  (N : Term_)
  (M : Term_)
  (L : Term_)
  (h1 : ¬ is_free_in x M)
  (h2 : is_sub_v2_alt x N M L) :
  M = L :=
  by
    induction h2
    case var_same y ih =>
      unfold is_free_in at h1
      contradiction
    case var_diff y ih =>
      apply Eq.refl
    case app P Q P' Q' ih_1 ih_2 ih_3 ih_4 =>
      unfold is_free_in at h1
      rewrite [not_or] at h1
      obtain ⟨h1_left, h1_right⟩ := h1
      specialize ih_3 h1_left
      specialize ih_4 h1_right
      rewrite [ih_3]
      rewrite [ih_4]
      apply Eq.refl
    case abs_1 y P ih =>
      apply Eq.refl
    case abs_2 y P ih_1 ih_2 =>
      apply Eq.refl
    case abs_3 y P P' ih_1 ih_2 ih_3 ih_4 =>
      unfold is_free_in at h1
      rewrite [not_and] at h1
      have s1 : P = P' :=
      by
        apply ih_4
        apply h1
        exact ih_1
      rewrite [s1]
      apply Eq.refl


theorem is_sub_v3_imp_is_sub_v2
  (x : String)
  (N : Term_)
  (M : Term_)
  (L : Term_)
  (h1 : is_sub_v3_alt x N M L) :
  is_sub_v2_alt x N M L :=
  by
    induction h1
    case var_same y ih =>
      apply is_sub_v2_alt.var_same
      exact ih
    case var_diff y ih =>
      apply is_sub_v2_alt.var_diff
      exact ih
    case app P Q P' Q' ih_1 ih_2 ih_3 ih_4 =>
      apply is_sub_v2_alt.app
      · exact ih_3
      · exact ih_4
    case abs_1 y P ih =>
      apply is_sub_v2_alt.abs_1
      exact ih
    case abs_2 y P P' ih_1 ih_2 ih_3 ih_4 =>
      have s1 : P = P' :=
      by
        exact extracted_1 x N P P' ih_2 ih_4
      rewrite [s1] at ih_2

      rewrite [s1]
      apply is_sub_v2_alt.abs_2
      · exact ih_1
      · exact ih_2
    case abs_3 y P P' ih_1 ih_2 ih_3 ih_4 =>
      apply is_sub_v2_alt.abs_3
      · exact ih_1
      · exact ih_2
      · exact ih_4


theorem is_sub_v2_iff_is_sub_v3
  (x : String)
  (N : Term_)
  (M : Term_)
  (L : Term_) :
  is_sub_v2_alt x N M L ↔ is_sub_v3_alt x N M L :=
  by
    constructor
    · apply is_sub_v2_imp_is_sub_v3
    · apply is_sub_v3_imp_is_sub_v2


-------------------------------------------------------------------------------
