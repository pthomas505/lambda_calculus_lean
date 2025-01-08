import LC.NV.UTLC.Term

import Mathlib.Data.Finset.Basic


set_option autoImplicit false


open Term_


/--
  `Term_.var_set M` := The set of all of the variables that have an occurrence in the term `M`.
-/
def Term_.var_set :
  Term_ → Finset Symbol_
  | var_ x => {x}
  | app_ P Q => P.var_set ∪ Q.var_set
  | abs_ x P => P.var_set ∪ {x}


/--
  `occurs_in v M` := True if and only if there is an occurrence of the variable `v` in the term `M`.
-/
def occurs_in
  (v : Symbol_) :
  Term_ → Prop
  | var_ x => v = x
  | app_ P Q => occurs_in v P ∨ occurs_in v Q
  | abs_ x P => v = x ∨ occurs_in v P


instance
  (v : Symbol_)
  (M : Term_) :
  Decidable (occurs_in v M) :=
  by
    induction M
    all_goals
      simp only [occurs_in]
      infer_instance


/--
  `Term_.bound_var_set M` := The set of all of the variables that have a bound occurrence in the term `M`.
-/
def Term_.bound_var_set :
  Term_ → Finset Symbol_
  | var_ _ => ∅
  | app_ P Q => P.bound_var_set ∪ Q.bound_var_set
  | abs_ x P => P.bound_var_set ∪ {x}


/--
  `is_bound_in v M` := True if and only if there is a bound occurrence of the variable `v` in the term `M`.
-/
def is_bound_in
  (v : Symbol_) :
  Term_ → Prop
  | var_ _ => False
  | app_ P Q => is_bound_in v P ∨ is_bound_in v Q
  | abs_ x P => v = x ∨ is_bound_in v P


instance
  (v : Symbol_)
  (M : Term_) :
  Decidable (is_bound_in v M) :=
  by
    induction M
    all_goals
      simp only [is_bound_in]
      infer_instance


/--
  `Term_.free_var_set M` := The set of all of the variables that have a free occurrence in the term `M`.
-/
def Term_.free_var_set :
  Term_ → Finset Symbol_
  | var_ x => {x}
  | app_ P Q => P.free_var_set ∪ Q.free_var_set
  | abs_ x P => P.free_var_set \ {x}


/--
  `is_free_in v M` := True if and only if there is a free occurrence of the variable `v` in the term `M`.
-/
def is_free_in
  (v : Symbol_) :
  Term_ → Prop
  | var_ x => v = x
  | app_ P Q => is_free_in v P ∨ is_free_in v Q
  | abs_ x P => ¬ v = x ∧ is_free_in v P


instance
  (v : Symbol_)
  (M : Term_) :
  Decidable (is_free_in v M) :=
  by
    induction M
    all_goals
      simp only [is_free_in]
      infer_instance


/--
  `Term_.is_open M` := True if and only if the term `M` contains a free occurrence of a variable.
-/
def Term_.is_open
  (M : Term_) :
  Prop :=
  ¬ M.free_var_set = ∅


instance
  (M : Term_) :
  Decidable M.is_open :=
  by
    simp only [is_open]
    infer_instance


/--
  `Term_.is_closed M` := True if and only if the term `M` does not contain a free occurrence of a variable.
-/
def Term_.is_closed
  (M : Term_) :
  Prop :=
  M.free_var_set = ∅


instance
  (M : Term_) :
  Decidable M.is_closed :=
  by
    simp only [is_closed]
    infer_instance


-------------------------------------------------------------------------------


theorem occurs_in_iff_mem_var_set
  (v : Symbol_)
  (M : Term_) :
  occurs_in v M ↔ v ∈ M.var_set :=
  by
    induction M
    all_goals
      simp only [occurs_in]
      simp only [Term_.var_set]
    case var_ x_ =>
      simp
    case app_ P_ Q_ ih_1 ih_2 =>
      rw [ih_1]
      rw [ih_2]
      simp
    case abs_ x_ P_ ih =>
      rw [ih]
      simp
      tauto


theorem is_bound_in_iff_mem_bound_var_set
  (v : Symbol_)
  (M : Term_) :
  is_bound_in v M ↔ v ∈ M.bound_var_set :=
  by
    induction M
    all_goals
      simp only [is_bound_in]
      simp only [Term_.bound_var_set]
    case var_ x_ =>
      simp
    case app_ P_ Q_ ih_1 ih_2 =>
      rw [ih_1]
      rw [ih_2]
      simp
    case abs_ x_ P_ ih =>
      rw [ih]
      simp
      tauto


theorem is_free_in_iff_mem_free_var_set
  (v : Symbol_)
  (M : Term_) :
  is_free_in v M ↔ v ∈ M.free_var_set :=
  by
    induction M
    all_goals
      simp only [is_free_in]
      simp only [Term_.free_var_set]
    case var_ x_ =>
      simp
    case app_ P_ Q_ ih_1 ih_2 =>
      rw [ih_1]
      rw [ih_2]
      simp
    case abs_ x_ P_ ih =>
      rw [ih]
      simp
      tauto


theorem is_bound_in_imp_occurs_in
  (v : Symbol_)
  (M : Term_)
  (h1 : is_bound_in v M) :
  occurs_in v M :=
  by
    induction M
    all_goals
      simp only [is_bound_in] at h1
    all_goals
      simp only [occurs_in]
      tauto


theorem is_free_in_imp_occurs_in
  (v : Symbol_)
  (M : Term_)
  (h1 : is_free_in v M) :
  occurs_in v M :=
  by
    induction M
    all_goals
      simp only [is_free_in] at h1
    all_goals
      simp only [occurs_in]
      tauto


theorem mem_bound_var_set_imp_mem_var_set
  (v : Symbol_)
  (M : Term_)
  (h1 : v ∈ M.bound_var_set) :
  v ∈ M.var_set :=
  by
    induction M
    all_goals
      simp only [bound_var_set] at h1
      simp only [var_set]
    case var_ x_ =>
      simp at h1
    case app_ P_ Q_ ih_1 ih_2 =>
      simp at h1
      simp
      tauto
    case abs_ x_ P_ ih =>
      simp at h1
      simp
      tauto


theorem not_mem_var_set_imp_not_mem_bound_var_set
  (v : Symbol_)
  (M : Term_)
  (h1 : v ∉ M.var_set) :
  v ∉ M.bound_var_set :=
  by
    intro contra
    apply h1
    exact mem_bound_var_set_imp_mem_var_set v M contra


theorem mem_free_var_set_imp_mem_var_set
  (v : Symbol_)
  (M : Term_)
  (h1 : v ∈ M.free_var_set) :
  v ∈ M.var_set :=
  by
    induction M
    all_goals
      simp only [free_var_set] at h1
      simp only [var_set]
    case var_ x_ =>
      exact h1
    case app_ P_ Q_ ih_1 ih_2 =>
      simp at h1
      simp
      tauto
    case abs_ x_ P_ ih =>
      simp at h1
      simp
      tauto


theorem not_mem_var_set_imp_not_mem_free_var_set
  (v : Symbol_)
  (M : Term_)
  (h1 : v ∉ M.var_set) :
  v ∉ M.free_var_set :=
  by
    intro contra
    apply h1
    exact mem_free_var_set_imp_mem_var_set v M contra


#lint
