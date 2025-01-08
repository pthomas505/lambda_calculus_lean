import LC.NV.UTLC.Reduce.NF


set_option autoImplicit false


open Term_


-- Applicative Order Reduction to Normal Form

-- In each step the leftmost of the innermost redexes is contracted, where an innermost redex is a redex not containing any redexes.

-- ?
inductive is_ao_small_step
  (sub : Symbol_ → Term_ → Term_ → Term_) :
  Term_ → Term_ → Prop
| rule_1
  (e1 e1' e2 : Term_) :
  is_ao_small_step sub e1 e1' →
  is_ao_small_step sub (app_ e1 e2) (app_ e1' e2)

| rule_2
  (e e' v : Term_) :
  is_abs v →
  is_ao_small_step sub e e' →
  is_ao_small_step sub (app_ v e) (app_ v e')

| rule_3
  (x : Symbol_)
  (e v : Term_) :
  is_abs v →
  is_ao_small_step sub (app_ (abs_ x e) v) (sub x v e)

| rule_4
  (x : Symbol_)
  (e e' : Term_) :
  is_ao_small_step sub e e' →
  is_ao_small_step sub (abs_ x e) (abs_ x e')


def ao_small_step
  (sub : Symbol_ → Term_ → Term_ → Term_) :
  Term_ → Option Term_

  -- rule_4
| abs_ x e =>
  match ao_small_step sub e with
  | Option.some e' => abs_ x e'
  | Option.none => Option.none

  -- rule_3
| app_ (abs_ x e) v@(abs_ _ _) => Option.some (sub x v e)

  -- rule_2
| app_ v@(abs_ _ _) e =>
  match ao_small_step sub e with
  | Option.some e' => app_ v e'
  | Option.none => Option.none

  -- rule_1
| app_ e1 e2 =>
  match ao_small_step sub e1 with
  | Option.some e1' => app_ e1' e2
  | Option.none => Option.none

| _ => Option.none


inductive is_ao_big_step
  (sub : Symbol_ → Term_ → Term_ → Term_) :
  Term_ → Term_ → Prop
| rule_1
  (x : Symbol_) :
  is_ao_big_step sub (var_ x) (var_ x)

| rule_2
  (x : Symbol_)
  (e e' : Term_) :
  is_ao_big_step sub e e' →
  is_ao_big_step sub (abs_ x e) (abs_ x e')

| rule_3
  (x : Symbol_)
  (e e' e1 e2 e2' : Term_) :
  is_ao_big_step sub e1 (abs_ x e) →
  is_ao_big_step sub e2 e2' →
  is_ao_big_step sub (sub x e2' e) e' →
  is_ao_big_step sub (app_ e1 e2) e'

| rule_4
  (e1 e1' e2 e2' : Term_) :
  ¬ is_abs e1' →
  is_ao_big_step sub e1 e1' →
  is_ao_big_step sub e2 e2' →
  is_ao_big_step sub (app_ e1 e2) (app_ e1' e2')
