import LambdaCalculusLean.NV.UTLC.Reduce.NF


set_option linter.style.longLine false
set_option linter.style.emptyLine false


-- Applicative Order Reduction to Normal Form

-- In each step the leftmost of the innermost redexes is contracted, where an innermost redex is a redex not containing any redexes.

-- ?
inductive is_ao_small_step
  (sub : String → Term_ → Term_ → Term_) :
  Term_ → Term_ → Prop
| rule_1
  (e1 e1' e2 : Term_) :
  is_ao_small_step sub e1 e1' →
  is_ao_small_step sub (Term_.App e1 e2) (Term_.App e1' e2)

| rule_2
  (e e' v : Term_) :
  Term_.is_abs v →
  is_ao_small_step sub e e' →
  is_ao_small_step sub (Term_.App v e) (Term_.App v e')

| rule_3
  (x : String)
  (e v : Term_) :
  Term_.is_abs v →
  is_ao_small_step sub (Term_.App (Term_.Abs x e) v) (sub x v e)

| rule_4
  (x : String)
  (e e' : Term_) :
  is_ao_small_step sub e e' →
  is_ao_small_step sub (Term_.Abs x e) (Term_.Abs x e')


def ao_small_step
  (sub : String → Term_ → Term_ → Term_) :
  Term_ → Option Term_

  -- rule_4
| Term_.Abs x e =>
  match ao_small_step sub e with
  | Option.some e' => Term_.Abs x e'
  | Option.none => Option.none

  -- rule_3
| Term_.App (Term_.Abs x e) v@(Term_.Abs _ _) => Option.some (sub x v e)

  -- rule_2
| Term_.App v@(Term_.Abs _ _) e =>
  match ao_small_step sub e with
  | Option.some e' => Term_.App v e'
  | Option.none => Option.none

  -- rule_1
| Term_.App e1 e2 =>
  match ao_small_step sub e1 with
  | Option.some e1' => Term_.App e1' e2
  | Option.none => Option.none

| _ => Option.none


inductive is_ao_big_step
  (sub : String → Term_ → Term_ → Term_) :
  Term_ → Term_ → Prop
| rule_1
  (x : String) :
  is_ao_big_step sub (Term_.Var x) (Term_.Var x)

| rule_2
  (x : String)
  (e e' : Term_) :
  is_ao_big_step sub e e' →
  is_ao_big_step sub (Term_.Abs x e) (Term_.Abs x e')

| rule_3
  (x : String)
  (e e' e1 e2 e2' : Term_) :
  is_ao_big_step sub e1 (Term_.Abs x e) →
  is_ao_big_step sub e2 e2' →
  is_ao_big_step sub (sub x e2' e) e' →
  is_ao_big_step sub (Term_.App e1 e2) e'

| rule_4
  (e1 e1' e2 e2' : Term_) :
  ¬ Term_.is_abs e1' →
  is_ao_big_step sub e1 e1' →
  is_ao_big_step sub e2 e2' →
  is_ao_big_step sub (Term_.App e1 e2) (Term_.App e1' e2')
