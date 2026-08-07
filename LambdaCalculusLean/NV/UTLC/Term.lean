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
