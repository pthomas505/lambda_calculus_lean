import LambdaCalculusLean.NV.UTLC.Comb
import LambdaCalculusLean.NV.UTLC.Reduce.NF
import LambdaCalculusLean.NV.UTLC.Sub.Sub


set_option linter.style.longLine false
set_option linter.style.emptyLine false


-- Call-by-Value Reduction to Weak Normal Form

-- Like applicative order, but no reductions are performed inside abstractions. Call-by-value reduction is the weak reduction strategy that reduces the leftmost innermost redex not inside a lambda abstraction.


inductive is_bv_small_step
  (sub : String → Term_ → Term_ → Term_) :
  Term_ → Term_ → Prop
| rule_1
  (e1 e1' e2 : Term_) :
  is_bv_small_step sub e1 e1' →
  is_bv_small_step sub (Term_.App e1 e2) (Term_.App e1' e2)

| rule_2
  (e e' v : Term_) :
  Term_.is_abs v →
  is_bv_small_step sub e e' →
  is_bv_small_step sub (Term_.App v e) (Term_.App v e')

| rule_3
  (x : String)
  (e v : Term_) :
  Term_.is_abs v →
  is_bv_small_step sub (Term_.App (Term_.Abs x e) v) (sub x v e)


def bv_small_step
  (sub : String → Term_ → Term_ → Term_) :
  Term_ → Option Term_

  -- rule_3
| Term_.App (Term_.Abs x e) v@(Term_.Abs _ _) => Option.some (sub x v e)

  -- rule_2
| Term_.App v@(Term_.Abs _ _) e =>
  match bv_small_step sub e with
  | Option.some e' => Term_.App v e'
  | Option.none => Option.none

  -- rule_1
| Term_.App e1 e2 =>
  match bv_small_step sub e1 with
  | Option.some e1' => Term_.App e1' e2
  | Option.none => Option.none

| _ => Option.none


example
  (sub : String → Term_ → Term_ → Term_)
  (M N : Term_)
  (h1 : is_bv_small_step sub M N) :
  bv_small_step sub M = Option.some N :=
  by
    induction h1
    case rule_1 e1 e1' e2 ih_1 ih_2 =>
      cases e1
      case Var e1_x =>
        cases ih_1
      case App e1_e1 e1_e2 =>
        unfold bv_small_step
        rewrite [ih_2]
        simp only
      case Abs e1_x e1_e =>
        cases ih_1
    case rule_2 e e' v ih_1 ih_2 ih_3 =>
      simp only [is_abs_iff_exists_abs] at ih_1
      obtain ⟨ih_1_x, ih_1_e, ih_1⟩ := ih_1
      rewrite [ih_1]
      cases e
      case Var e_x =>
        cases ih_2
      case App e_e1 e_e2 =>
        unfold bv_small_step
        rewrite [ih_3]
        simp only
      case Abs e_x e_e =>
        cases ih_2
    case rule_3 x e v ih_1 =>
      simp only [is_abs_iff_exists_abs] at ih_1
      obtain ⟨ih_1_x, ih_1_e, ih_1⟩ := ih_1
      rewrite [ih_1]
      unfold bv_small_step
      apply Eq.refl


example
  (sub : String → Term_ → Term_ → Term_)
  (M N : Term_)
  (h1 : bv_small_step sub M = Option.some N) :
  is_bv_small_step sub M N :=
  by
    induction M generalizing N
    case Var x =>
      unfold bv_small_step at h1
      contradiction
    case App e1 e2 ih_1 ih_2 =>
      cases e1
      case Var e1_x =>
        cases h1
      case App e1_e1 e1_e2 =>
        unfold bv_small_step at h1
        cases h : bv_small_step sub (e1_e1.App e1_e2)
        case none =>
          rewrite [h] at h1
          simp only at h1
          contradiction
        case some val =>
          rewrite [h] at h1
          simp only at h1
          simp only [Option.some.injEq] at h1
          rw [← h1]
          specialize ih_1 val h
          exact is_bv_small_step.rule_1 (e1_e1.App e1_e2) val e2 ih_1
      case Abs e1_x e1_e =>
        cases e2
        case Var e2_x =>
          unfold bv_small_step at h1
          cases h1
        case App e2_e1 e2_e2 =>
          unfold bv_small_step at h1
          cases h : bv_small_step sub (e2_e1.App e2_e2)
          case none =>
            rewrite [h] at h1
            simp only at h1
            contradiction
          case some val =>
            rewrite [h] at h1
            simp only at h1
            simp only [Option.some.injEq] at h1
            specialize ih_2 val h
            rewrite [← h1]
            apply is_bv_small_step.rule_2
            · unfold Term_.is_abs
              simp only
            · exact ih_2
        case Abs e2_x e2_e =>
          unfold bv_small_step at h1
          simp only [Option.some.injEq] at h1
          rewrite [← h1]
          apply is_bv_small_step.rule_3
          unfold Term_.is_abs
          simp only
    case Abs x e _ =>
      unfold bv_small_step at h1
      contradiction


def iterate_bv_small_step
  (sub : String → Term_ → Term_ → Term_)
  (fuel : Nat)
  (e : Term_) :
  Term_ :=
  if fuel > 0
  then
    match bv_small_step sub e with
    | Option.some next => iterate_bv_small_step sub (fuel - 1) next
    | Option.none => e
  else e


#eval iterate_bv_small_step (fun x y z => sub_single x y z '+') 3 (Term_.App not_ true_) = false_
#eval iterate_bv_small_step (fun x y z => sub_single x y z '+') 3 (Term_.App not_ false_) = true_


inductive is_bv_big_step
  (sub : String → Term_ → Term_ → Term_) :
  Term_ → Term_ → Prop
| rule_1
  (x : String) :
  is_bv_big_step sub (Term_.Var x) (Term_.Var x)

| rule_2
  (x : String)
  (e : Term_) :
  is_bv_big_step sub (Term_.Abs x e) (Term_.Abs x e)

| rule_3
  (x : String)
  (e e' e1 e2 e2' : Term_) :
  is_bv_big_step sub e1 (Term_.Abs x e) →
  is_bv_big_step sub e2 e2' →
  is_bv_big_step sub (sub x e2' e) e' →
  is_bv_big_step sub (Term_.App e1 e2) e'

| rule_4
  (e1 e1' e2 e2' : Term_) :
  ¬ Term_.is_abs e1' →
  is_bv_big_step sub e1 e1' →
  is_bv_big_step sub e2 e2' →
  is_bv_big_step sub (Term_.App e1 e2) (Term_.App e1' e2')


example
  (sub : String → Term_ → Term_ → Term_)
  (M N : Term_)
  (h1 : Relation.ReflTransGen (is_bv_small_step sub) M N)
  (h2 : is_weak_head_normal_form N) :
  is_bv_big_step sub M N :=
  by
    induction h1
    case refl =>
      induction M
      case Var x =>
        apply is_bv_big_step.rule_1
      case App e1 e2 ih_1 ih_2 =>
        induction e1
        case Var e1_x =>
          induction e2
          case Var e2_x =>
            apply is_bv_big_step.rule_4
            · unfold Term_.is_abs
              simp only
              intro contra
              contradiction
            · apply is_bv_big_step.rule_1
            · apply ih_2
              unfold is_weak_head_normal_form
              simp only
          case App e2_e1 e2_e2 =>
            apply is_bv_big_step.rule_4
            · unfold Term_.is_abs
              simp only
              intro contra
              contradiction
            · apply is_bv_big_step.rule_1
            · apply ih_2
              unfold is_weak_head_normal_form
              simp only
              sorry
          sorry
        case App e1_e1 e1_e2 =>
          apply is_bv_big_step.rule_4
          · unfold Term_.is_abs
            intro contra
            contradiction
          · sorry
          · sorry
        unfold is_weak_head_normal_form at h2
        simp only at h2
        unfold is_neutral_weak_head_normal_form at h2
        sorry
      sorry
    sorry
