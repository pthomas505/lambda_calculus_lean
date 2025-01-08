import LC.NV.UTLC.Term

import Mathlib.Data.Multiset.Basic


set_option autoImplicit false


open Term_


/--
  `Term_.subterm_set M` := The set of all of the subterms of a term `M`.
  [2] Definition 1.3.5
-/
def Term_.subterm_set :
  Term_ → Multiset Term_
  | var_ x => {var_ x}
  | app_ P Q => P.subterm_set ∪ Q.subterm_set ∪ {app_ P Q}
  | abs_ x P => P.subterm_set ∪ {abs_ x P}


-- [2] reflexivity
lemma lemma_1_3_6_refl
  (M : Term_) :
  M ∈ M.subterm_set :=
  by
    cases M
    all_goals
      unfold subterm_set
    case var_ x_ =>
      simp
    case app_ P_ Q_ =>
      simp
    case abs_ x_ P_ =>
      simp


-- [2] transitivity
lemma lemma_1_3_6_trans
  (M M' M'' : Term_)
  (h1 : M ∈ M'.subterm_set)
  (h2 : M' ∈ M''.subterm_set) :
  M ∈ M''.subterm_set :=
  by
    induction M''
    case var_ x_ =>
      unfold subterm_set at h2
      simp at h2
      rw [h2] at h1
      exact h1
    case app_ P_ Q_ ih_1 ih_2 =>
      unfold subterm_set at h2
      simp at h2

      cases h2
      case inl h2 =>
        cases h2
        case inl h2 =>
          unfold subterm_set
          simp
          left
          left
          exact ih_1 h2
        case inr h2 =>
          unfold subterm_set
          simp
          left
          right
          exact ih_2 h2
      case inr h2 =>
        rw [h2] at h1
        exact h1
    case abs_ x_ P_ ih =>
      unfold subterm_set at h2
      simp at h2

      cases h2
      case inl h2 =>
        unfold subterm_set
        simp
        left
        exact ih h2
      case inr h2 =>
        rw [h2] at h1
        exact h1


/--
  [2] Definition 1.3.8
-/
def is_proper_subterm
  (M M' : Term_) :
  Prop :=
  M ∈ M'.subterm_set ∧ ¬ M = M'


#lint
