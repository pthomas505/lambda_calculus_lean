import TtfpLean.UTLC.Term

import Mathlib.Data.Finset.Basic


set_option linter.style.docString false
set_option linter.style.longLine false
set_option linter.style.emptyLine false


/--
  `Term_.var_set M` := The set of all of the variables that have an occurrence in the term `M`.
-/
def Term_.var_set : Term_ → Finset String
  | Var x => {x}
  | App M N => M.var_set ∪ N.var_set
  | Abs x M => {x} ∪ M.var_set


/--
  `occurs_in x M` := True if and only if there is an occurrence of the variable `x` in the term `M`.
-/
def occurs_in
  (x : String) :
  Term_ → Prop
  | Term_.Var v => x = v
  | Term_.App P Q => occurs_in x P ∨ occurs_in x Q
  | Term_.Abs v P => x = v ∨ occurs_in x P

instance
  (x : String)
  (M : Term_) :
  Decidable (occurs_in x M) :=
  by
    induction M
    all_goals
      unfold occurs_in
      infer_instance


-- ----------------------------------------------------------------------------


/--
  `Term_.binder_var_set M` := The set of all of the variables that have an occurrence as a binder in the term `M`.
-/
def Term_.binder_var_set : Term_ → Finset String
  | Var _ => ∅
  | App M N => M.binder_var_set ∪ N.binder_var_set
  | Abs x M => {x} ∪ M.binder_var_set


/--
  `is_binder_in x M` := True if and only if there is an occurrence of the variable `x` as a binder in the term `M`.
-/
def is_binder_in
  (x : String) :
  Term_ → Prop
  | Term_.Var _ => False
  | Term_.App P Q => is_binder_in x P ∨ is_binder_in x Q
  | Term_.Abs v P => x = v ∨ is_binder_in x P

instance
  (x : String)
  (M : Term_) :
  Decidable (is_binder_in x M) :=
  by
    induction M
    all_goals
      unfold is_binder_in
      infer_instance


-- ----------------------------------------------------------------------------


/--
  `Term_.free_var_set M` := The set of all of the variables that have a free occurrence in the term `M`.
  Definition 1.4.1
-/
def Term_.free_var_set : Term_ → Finset String
  | Var x => {x}
  | App M N => M.free_var_set ∪ N.free_var_set
  | Abs x M => M.free_var_set \ {x}


/--
  `is_free_in x M` := True if and only if there is a free occurrence of the variable `x` in the term `M`.
-/
def is_free_in
  (x : String) :
  Term_ → Prop
  | Term_.Var v => x = v
  | Term_.App P Q => is_free_in x P ∨ is_free_in x Q
  | Term_.Abs v P => ¬ x = v ∧ is_free_in x P

instance
  (x : String)
  (M : Term_) :
  Decidable (is_free_in x M) :=
  by
    induction M
    all_goals
      unfold is_free_in
      infer_instance


-- ----------------------------------------------------------------------------


theorem occurs_in_iff_mem_var_set
  (x : String)
  (M : Term_) :
  occurs_in x M ↔ x ∈ M.var_set :=
  by
    induction M
    all_goals
      unfold occurs_in
      unfold Term_.var_set
    case Var v =>
      rewrite [Finset.mem_singleton]
      apply Iff.refl
    case App P Q ih_1 ih_2 =>
      rewrite [ih_1]
      rewrite [ih_2]
      rewrite [Finset.mem_union]
      apply Iff.refl
    case Abs v P ih =>
      rewrite [ih]
      rewrite [Finset.mem_union, Finset.mem_singleton]
      apply Iff.refl


theorem is_binder_in_iff_mem_binder_var_set
  (x : String)
  (M : Term_) :
  is_binder_in x M ↔ x ∈ M.binder_var_set :=
  by
    induction M
    all_goals
      unfold is_binder_in
      unfold Term_.binder_var_set
    case Var v =>
      simp only [Finset.notMem_empty]
    case App P Q ih_1 ih_2 =>
      rewrite [ih_1]
      rewrite [ih_2]
      rewrite [Finset.mem_union]
      apply Iff.refl
    case Abs v P ih =>
      rewrite [ih]
      rewrite [Finset.mem_union, Finset.mem_singleton]
      apply Iff.refl


theorem is_free_in_iff_mem_free_var_set
  (x : String)
  (M : Term_) :
  is_free_in x M ↔ x ∈ M.free_var_set :=
  by
    induction M
    all_goals
      unfold is_free_in
      unfold Term_.free_var_set
    case Var v =>
      rewrite [Finset.mem_singleton]
      apply Iff.refl
    case App P Q ih_1 ih_2 =>
      rewrite [ih_1]
      rewrite [ih_2]
      rewrite [Finset.mem_union]
      apply Iff.refl
    case Abs v P ih =>
      rewrite [ih]
      rewrite [Finset.mem_sdiff, Finset.mem_singleton]
      rewrite [And.comm]
      apply Iff.refl


-- ----------------------------------------------------------------------------


theorem is_free_in_imp_occurs_in
  (x : String)
  (M : Term_)
  (h1 : is_free_in x M) :
  occurs_in x M :=
  by
  induction M
  case Var v =>
    exact h1
  case App P Q ih_1 ih_2 =>
    unfold is_free_in at h1

    unfold occurs_in
    cases h1
    case inl h1 =>
      left
      exact ih_1 h1
    case inr h1 =>
      right
      exact ih_2 h1
  case Abs v P ih =>
    unfold is_free_in at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    unfold occurs_in
    right
    exact ih h1_right


theorem is_binder_in_imp_occurs_in
  (x : String)
  (M : Term_)
  (h1 : is_binder_in x M) :
  occurs_in x M :=
  by
  induction M
  case Var v =>
    unfold is_binder_in at h1
    contradiction
  case App P Q ih_1 ih_2 =>
    unfold is_binder_in at h1

    unfold occurs_in
    cases h1
    case inl h1 =>
      left
      exact ih_1 h1
    case inr h1 =>
      right
      exact ih_2 h1
  case Abs v P ih =>
    unfold is_binder_in at h1

    unfold occurs_in
    cases h1
    case inl h1 =>
      left
      exact h1
    case inr h1 =>
      right
      exact ih h1


theorem occurs_in_imp_is_binder_in_or_is_free_in
  (x : String)
  (M : Term_)
  (h1 : occurs_in x M) :
  is_binder_in x M ∨ is_free_in x M :=
  by
  induction M
  case Var v =>
    unfold occurs_in at h1

    right
    unfold is_free_in
    exact h1
  case App P Q ih_1 ih_2 =>
    unfold occurs_in at h1

    unfold is_binder_in
    unfold is_free_in
    cases h1
    case inl h1 =>
      specialize ih_1 h1
      cases ih_1
      case inl ih_1 =>
        left
        left
        exact ih_1
      case inr ih_1 =>
        right
        left
        exact ih_1
    case inr h1 =>
      specialize ih_2 h1
      cases ih_2
      case inl ih_2 =>
        left
        right
        exact ih_2
      case inr ih_2 =>
        right
        right
        exact ih_2
  case Abs v P ih =>
    unfold occurs_in at h1

    unfold is_binder_in
    unfold is_free_in
    cases h1
    case inl h1 =>
      left
      left
      exact h1
    case inr h1 =>
      specialize ih h1
      cases ih
      case inl ih =>
        left
        right
        exact ih
      case inr ih =>
        by_cases c1 : x = v
        case pos =>
          left
          left
          exact c1
        case neg =>
          right
          constructor
          · exact c1
          · exact ih


theorem occurs_in_iff_is_binder_in_or_is_free_in
  (x : String)
  (M : Term_) :
  occurs_in x M ↔ (is_binder_in x M ∨ is_free_in x M) :=
  by
  constructor
  · apply occurs_in_imp_is_binder_in_or_is_free_in
  · intro a1
    cases a1
    case inl a1 =>
      apply is_binder_in_imp_occurs_in
      exact a1
    case inr a1 =>
      apply is_free_in_imp_occurs_in
      exact a1


-- ----------------------------------------------------------------------------


/--
  `Term_.is_closed M` := True if and only if the term `M` does not contain the free occurrence of any variable.
  Definition 1.4.3
-/
def Term_.is_closed
  (M : Term_) :
  Prop :=
  M.free_var_set = ∅

instance
  (M : Term_) :
  Decidable M.is_closed :=
  by
    unfold Term_.is_closed
    infer_instance
