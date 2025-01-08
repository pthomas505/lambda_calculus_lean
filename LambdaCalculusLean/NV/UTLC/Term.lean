import Mathlib.Tactic


set_option autoImplicit false


-- untyped lambda calculus


/--
  The type of symbols.
-/
@[reducible]
def Symbol_ : Type := String
deriving Inhabited, DecidableEq, Repr


/--
  The type of terms.
-/
inductive Term_ : Type
  | var_ : Symbol_ → Term_
  | app_ : Term_ → Term_ → Term_
  | abs_ : Symbol_ → Term_ → Term_
deriving Inhabited, DecidableEq, Repr

compile_inductive% Term_

open Term_


/--
  The string representation of terms.
-/
def Term_.toString : Term_ → String
  | var_ x => x
  | app_ P Q => s! "({P.toString} {Q.toString})"
  | abs_ x P => s! "(fun {x}. {P.toString})"


instance :
  ToString Term_ :=
  { toString := fun (M : Term_) => M.toString }


/--
  `is_var M` := True if and only if `M` is a term variable.
-/
def Term_.is_var :
  Term_ → Prop
  | var_ _ => True
  | _ => False


instance
  (M : Term_) :
  Decidable M.is_var :=
  by
    cases M
    all_goals
      unfold is_var
      infer_instance


lemma is_var_iff_exists_var
  (M : Term_) :
  M.is_var ↔ ∃ (x : Symbol_), M = var_ x :=
  by
    constructor
    · intro a1
      cases M
      case var_ x =>
        apply Exists.intro x
        rfl
      all_goals
        unfold is_var at a1
        simp only at a1
    · intro a1
      obtain ⟨x, a1⟩ := a1
      rw [a1]
      unfold is_var
      simp only


/--
  `is_app M` := True if and only if `M` is a term application.
-/
def Term_.is_app :
  Term_ → Prop
  | app_ _ _ => True
  | _ => False


instance
  (M : Term_) :
  Decidable M.is_app :=
  by
    cases M
    all_goals
      unfold is_app
      infer_instance


lemma is_app_iff_exists_app
  (M : Term_) :
  M.is_app ↔∃ (P Q : Term_), M = app_ P Q :=
  by
    constructor
    · intro a1
      cases M
      case app_ P Q =>
        apply Exists.intro P
        apply Exists.intro Q
        rfl
      all_goals
        unfold is_app at a1
        simp only at a1
    · intro a1
      obtain ⟨P, Q, a1⟩ := a1
      rw [a1]
      unfold is_app
      simp only


/--
  `is_abs M` := True if and only if `M` is a term abstraction.
-/
def Term_.is_abs :
  Term_ → Prop
  | abs_ _ _ => True
  | _ => False


instance
  (M : Term_) :
  Decidable M.is_abs :=
  by
    cases M
    all_goals
      unfold is_abs
      infer_instance


lemma is_abs_iff_exists_abs
  (M : Term_) :
  M.is_abs ↔∃ (x : Symbol_) (P : Term_), M = abs_ x P :=
  by
    constructor
    · intro a1
      cases M
      case abs_ x P =>
        apply Exists.intro x
        apply Exists.intro P
        rfl
      all_goals
        unfold is_abs at a1
        simp only at a1
    · intro a1
      obtain ⟨P, Q, a1⟩ := a1
      rw [a1]
      unfold is_abs
      simp only


#lint
