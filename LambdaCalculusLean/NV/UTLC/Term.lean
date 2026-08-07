import Lean.Syntax
import Lean.Meta
import Lean.Elab

import Mathlib.Util.CompileInductive


set_option linter.style.emptyLine false
set_option linter.style.docString false


/--
  The type of terms.
-/
inductive Term_ : Type
  | Var : String → Term_
  | App : Term_ → Term_ → Term_
  | Abs : String → Term_ → Term_
deriving Inhabited, DecidableEq, Repr

compile_inductive% Term_


/--
  The string representation of terms.
-/
def Term_.toString : Term_ → String
  | Var x => x
  | App M N => s! "({M.toString} {N.toString})"
  | Abs x M => s! "(λ {x}. {M.toString})"

instance : ToString Term_ := ⟨Term_.toString⟩


declare_syntax_cat term_

syntax ident : term_
syntax "(" term_ term_ ")" : term_
syntax "(" "λ" ident "." term_ ")" : term_


partial def elabTerm :
  Lean.Syntax → Lean.Meta.MetaM Lean.Expr

  -- Var
  | `(term_| $x:ident) => do
    let x' : Lean.Expr := Lean.mkStrLit x.getId.toString
    Lean.Meta.mkAppM ``Term_.Var #[x']

  -- App
  | `(term_| ( $e1 $e2 )) => do
    let e1' : Lean.Expr ← elabTerm e1
    let e2' : Lean.Expr ← elabTerm e2
    Lean.Meta.mkAppM ``Term_.App #[e1', e2']

  -- Abs
  | `(term_| ( λ $x . $e )) => do
    let x' : Lean.Expr := Lean.mkStrLit x.getId.toString
    let e' : Lean.Expr ← elabTerm e
    Lean.Meta.mkAppM ``Term_.Abs #[x', e']

  | _ => Lean.Elab.throwUnsupportedSyntax

elab "(Term_|" e:term_ ")" : term => elabTerm e


#eval (Term_| x)
#eval (Term_| x).toString

#eval (Term_| (x y))
#eval (Term_| (x y)).toString

#eval (Term_| (λ x. x))
#eval (Term_| (λ x. x)).toString


-- ----------------------------------------------------------------------------


/--
  `Term_.is_var M` := True if and only if `M` is a term variable.
-/
def Term_.is_var :
  Term_ → Prop
  | Term_.Var _ => True
  | _ => False


instance
  (M : Term_) :
  Decidable M.is_var :=
  by
    cases M
    all_goals
      unfold Term_.is_var
      infer_instance


lemma is_var_iff_exists_var
  (M : Term_) :
  M.is_var ↔ ∃ (x : String), M = Term_.Var x :=
  by
    constructor
    · intro a1
      cases M
      case Var x =>
        apply Exists.intro x
        apply Eq.refl
      all_goals
        unfold Term_.is_var at a1
        simp only at a1
    · intro a1
      obtain ⟨x, a1⟩ := a1
      rewrite [a1]
      unfold Term_.is_var
      simp only


/--
  `Term_.is_app M` := True if and only if `M` is a term application.
-/
def Term_.is_app :
  Term_ → Prop
  | Term_.App _ _ => True
  | _ => False


instance
  (M : Term_) :
  Decidable M.is_app :=
  by
    cases M
    all_goals
      unfold Term_.is_app
      infer_instance


lemma is_app_iff_exists_app
  (M : Term_) :
  M.is_app ↔∃ (P Q : Term_), M = Term_.App P Q :=
  by
    constructor
    · intro a1
      cases M
      case App P Q =>
        apply Exists.intro P
        apply Exists.intro Q
        apply Eq.refl
      all_goals
        unfold Term_.is_app at a1
        simp only at a1
    · intro a1
      obtain ⟨P, Q, a1⟩ := a1
      rewrite [a1]
      unfold Term_.is_app
      simp only


/--
  `Term_.is_abs M` := True if and only if `M` is a term abstraction.
-/
def Term_.is_abs :
  Term_ → Prop
  | Term_.Abs _ _ => True
  | _ => False


instance
  (M : Term_) :
  Decidable M.is_abs :=
  by
    cases M
    all_goals
      unfold Term_.is_abs
      infer_instance


lemma is_abs_iff_exists_abs
  (M : Term_) :
  M.is_abs ↔∃ (x : String) (P : Term_), M = Term_.Abs x P :=
  by
    constructor
    · intro a1
      cases M
      case Abs x P =>
        apply Exists.intro x
        apply Exists.intro P
        apply Eq.refl
      all_goals
        unfold Term_.is_abs at a1
        simp only at a1
    · intro a1
      obtain ⟨P, Q, a1⟩ := a1
      rewrite [a1]
      unfold Term_.is_abs
      simp only
