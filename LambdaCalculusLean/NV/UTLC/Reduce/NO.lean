import LC.NV.UTLC.Comb
import LC.NV.UTLC.Reduce.NF
import LC.NV.UTLC.Sub.Sub


set_option autoImplicit false


open Term_


-- Normal Order Reduction to Normal Form

-- In each step the leftmost of the outermost redexes is contracted, where an outermost redex is a redex not contained in any redexes.

-- ?
inductive is_no_small_step
  (sub : Symbol_ → Term_ → Term_ → Term_) :
  Term_ → Term_ → Prop
| rule_1
  (e1 e1' e2 : Term_) :
  is_no_small_step sub e1 e1' →
  is_no_small_step sub (app_ e1 e2) (app_ e1' e2)

| rule_2
  (x : Symbol_)
  (e1 e2 : Term_) :
  is_no_small_step sub (app_ (abs_ x e1) e2) (sub x e2 e1)

| rule_3
  (x : Symbol_)
  (e e' : Term_) :
  is_no_small_step sub e e' →
  is_no_small_step sub (abs_ x e) (abs_ x e')


def no_small_step
  (sub : Symbol_ → Term_ → Term_ → Term_) :
  Term_ → Option Term_

  -- rule_3
| abs_ x e =>
  match no_small_step sub e with
  | Option.some e' => abs_ x e'
  | Option.none => Option.none

  -- rule_2
| app_ (abs_ x e1) e2 => Option.some (sub x e2 e1)

  -- rule_1
| app_ e1 e2 =>
  match no_small_step sub e1 with
  | Option.some e1' => app_ e1' e2
  | Option.none => Option.none

| _ => Option.none


inductive is_no_big_step
  (sub : Symbol_ → Term_ → Term_ → Term_) :
  Term_ → Term_ → Prop
| rule_1
  (x : Symbol_) :
  is_no_big_step sub (var_ x) (var_ x)

| rule_2
  (x : Symbol_)
  (e e' : Term_) :
  is_no_big_step sub e e' →
  is_no_big_step sub (abs_ x e) (abs_ x e')

| rule_3
  (x : Symbol_)
  (e e' e1 e2 : Term_) :
  is_no_big_step sub e1 (abs_ x e) →
  is_no_big_step sub (sub x e2 e) e' →
  is_no_big_step sub (app_ e1 e2) e'

| rule_4
  (e1 e1' e1'' e2 e2' : Term_) :
  ¬ is_abs e1' →
  is_no_big_step sub e1 e1' →
  is_no_big_step sub e1' e1'' →
  is_no_big_step sub e2 e2' →
  is_no_big_step sub (app_ e1 e2) (app_ e1'' e2')
