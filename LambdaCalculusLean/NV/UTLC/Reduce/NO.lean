import LambdaCalculusLean.NV.UTLC.Comb
import LambdaCalculusLean.NV.UTLC.Reduce.NF
import LambdaCalculusLean.NV.UTLC.Sub.Sub


set_option linter.style.longLine false
set_option linter.style.emptyLine false


-- Normal Order Reduction to Normal Form

-- In each step the leftmost of the outermost redexes is contracted, where an outermost redex is a redex not contained in any redexes.

-- ?
inductive is_no_small_step
  (sub : String → Term_ → Term_ → Term_) :
  Term_ → Term_ → Prop
| rule_1
  (e1 e1' e2 : Term_) :
  is_no_small_step sub e1 e1' →
  is_no_small_step sub (Term_.App e1 e2) (Term_.App e1' e2)

| rule_2
  (x : String)
  (e1 e2 : Term_) :
  is_no_small_step sub (Term_.App (Term_.Abs x e1) e2) (sub x e2 e1)

| rule_3
  (x : String)
  (e e' : Term_) :
  is_no_small_step sub e e' →
  is_no_small_step sub (Term_.Abs x e) (Term_.Abs x e')


def no_small_step
  (sub : String → Term_ → Term_ → Term_) :
  Term_ → Option Term_

  -- rule_3
| Term_.Abs x e =>
  match no_small_step sub e with
  | Option.some e' => Term_.Abs x e'
  | Option.none => Option.none

  -- rule_2
| Term_.App (Term_.Abs x e1) e2 => Option.some (sub x e2 e1)

  -- rule_1
| Term_.App e1 e2 =>
  match no_small_step sub e1 with
  | Option.some e1' => Term_.App e1' e2
  | Option.none => Option.none

| _ => Option.none


inductive is_no_big_step
  (sub : String → Term_ → Term_ → Term_) :
  Term_ → Term_ → Prop
| rule_1
  (x : String) :
  is_no_big_step sub (Term_.Var x) (Term_.Var x)

| rule_2
  (x : String)
  (e e' : Term_) :
  is_no_big_step sub e e' →
  is_no_big_step sub (Term_.Abs x e) (Term_.Abs x e')

| rule_3
  (x : String)
  (e e' e1 e2 : Term_) :
  is_no_big_step sub e1 (Term_.Abs x e) →
  is_no_big_step sub (sub x e2 e) e' →
  is_no_big_step sub (Term_.App e1 e2) e'

| rule_4
  (e1 e1' e1'' e2 e2' : Term_) :
  ¬ Term_.is_abs e1' →
  is_no_big_step sub e1 e1' →
  is_no_big_step sub e1' e1'' →
  is_no_big_step sub e2 e2' →
  is_no_big_step sub (Term_.App e1 e2) (Term_.App e1'' e2')
