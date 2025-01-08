import LC.NV.UTLC.Comb
import LC.NV.UTLC.Reduce.NF
import LC.NV.UTLC.Sub.Sub


set_option autoImplicit false


open Term_


-- full beta reduction

-- Any redex can be reduced at any time.


inductive is_full_step
  (sub : Symbol_ → Term_ → Term_ → Term_) :
  Term_ → Term_ → Prop
| rule_1
  (e1 e1' e2 : Term_) :
  is_full_step sub e1 e1' →
  is_full_step sub (app_ e1 e2) (app_ e1' e2)

| rule_2
  (e1 e2 e2' : Term_) :
  is_full_step sub e2 e2' →
  is_full_step sub (app_ e1 e2) (app_ e1 e2')

| rule_3
  (x : Symbol_)
  (e e' : Term_) :
  is_full_step sub e e' →
  is_full_step sub (abs_ x e) (abs_ x e')

| rule_4
  (x : Symbol_)
  (e1 e2 : Term_) :
  is_full_step sub (app_ (abs_ x e1) e2) (sub x e2 e1)
