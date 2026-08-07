import LambdaCalculusLean.NV.UTLC.Comb
import LambdaCalculusLean.NV.UTLC.Reduce.NF
import LambdaCalculusLean.NV.UTLC.Sub.Sub


set_option linter.style.emptyLine false


-- full beta reduction

-- Any redex can be reduced at any time.


inductive is_full_step
  (sub : String → Term_ → Term_ → Term_) :
  Term_ → Term_ → Prop
| rule_1
  (e1 e1' e2 : Term_) :
  is_full_step sub e1 e1' →
  is_full_step sub (Term_.App e1 e2) (Term_.App e1' e2)

| rule_2
  (e1 e2 e2' : Term_) :
  is_full_step sub e2 e2' →
  is_full_step sub (Term_.App e1 e2) (Term_.App e1 e2')

| rule_3
  (x : String)
  (e e' : Term_) :
  is_full_step sub e e' →
  is_full_step sub (Term_.Abs x e) (Term_.Abs x e')

| rule_4
  (x : String)
  (e1 e2 : Term_) :
  is_full_step sub (Term_.App (Term_.Abs x e1) e2) (sub x e2 e1)
