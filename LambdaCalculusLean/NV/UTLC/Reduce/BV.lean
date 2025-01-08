import LC.NV.UTLC.Comb
import LC.NV.UTLC.Reduce.NF
import LC.NV.UTLC.Sub.Sub


set_option autoImplicit false


open Term_


-- Call-by-Value Reduction to Weak Normal Form

-- Like applicative order, but no reductions are performed inside abstractions. Call-by-value reduction is the weak reduction strategy that reduces the leftmost innermost redex not inside a lambda abstraction.


inductive is_bv_small_step
  (sub : Symbol_ → Term_ → Term_ → Term_) :
  Term_ → Term_ → Prop
| rule_1
  (e1 e1' e2 : Term_) :
  is_bv_small_step sub e1 e1' →
  is_bv_small_step sub (app_ e1 e2) (app_ e1' e2)

| rule_2
  (e e' v : Term_) :
  is_abs v →
  is_bv_small_step sub e e' →
  is_bv_small_step sub (app_ v e) (app_ v e')

| rule_3
  (x : Symbol_)
  (e v : Term_) :
  is_abs v →
  is_bv_small_step sub (app_ (abs_ x e) v) (sub x v e)


def bv_small_step
  (sub : Symbol_ → Term_ → Term_ → Term_) :
  Term_ → Option Term_

  -- rule_3
| app_ (abs_ x e) v@(abs_ _ _) => Option.some (sub x v e)

  -- rule_2
| app_ v@(abs_ _ _) e =>
  match bv_small_step sub e with
  | Option.some e' => app_ v e'
  | Option.none => Option.none

  -- rule_1
| app_ e1 e2 =>
  match bv_small_step sub e1 with
  | Option.some e1' => app_ e1' e2
  | Option.none => Option.none

| _ => Option.none


example
  (sub : Symbol_ → Term_ → Term_ → Term_)
  (M N : Term_)
  (h1 : is_bv_small_step sub M N) :
  bv_small_step sub M = Option.some N :=
  by
    induction h1
    case rule_1 e1 e1' e2 ih_1 ih_2 =>
      cases e1
      case var_ e1_x =>
        cases ih_1
      case app_ e1_e1 e1_e2 =>
        unfold bv_small_step
        rw [ih_2]
      case abs_ e1_x e1_e =>
        cases ih_1
    case rule_2 e e' v ih_1 ih_2 ih_3 =>
      simp only [is_abs_iff_exists_abs] at ih_1
      obtain ⟨ih_1_x, ih_1_e, ih_1⟩ := ih_1
      rw [ih_1]
      cases e
      case var_ e_x =>
        cases ih_2
      case app_ e_e1 e_e2 =>
        unfold bv_small_step
        rw [ih_3]
      case abs_ e_x e_e =>
        unfold bv_small_step
        cases ih_2
    case rule_3 x e v ih_1 =>
      simp only [is_abs_iff_exists_abs] at ih_1
      obtain ⟨ih_1_x, ih_1_e, ih_1⟩ := ih_1
      rw [ih_1]
      unfold bv_small_step
      rfl


example
  (sub : Symbol_ → Term_ → Term_ → Term_)
  (M N : Term_)
  (h1 : bv_small_step sub M = Option.some N) :
  is_bv_small_step sub M N :=
  by
    induction M generalizing N
    case var_ x =>
      unfold bv_small_step at h1
      simp at h1
    case app_ e1 e2 ih_1 ih_2 =>
      cases e1
      case var_ e1_x =>
        cases h1
      case app_ e1_e1 e1_e2 =>
        unfold bv_small_step at h1
        cases h : bv_small_step sub (e1_e1.app_ e1_e2)
        case none =>
          rw [h] at h1
          simp at h1
        case some val =>
          rw [h] at h1
          simp at h1
          specialize ih_1 val h
          rw [← h1]
          exact is_bv_small_step.rule_1 (e1_e1.app_ e1_e2) val e2 ih_1
      case abs_ e1_x e1_e =>
        cases e2
        case var_ e2_x =>
          unfold bv_small_step at h1
          cases h1
        case app_ e2_e1 e2_e2 =>
          unfold bv_small_step at h1
          cases h : bv_small_step sub (e2_e1.app_ e2_e2)
          case none =>
            rw [h] at h1
            simp at h1
          case some val =>
            rw [h] at h1
            simp at h1
            specialize ih_2 val h
            rw [← h1]
            apply is_bv_small_step.rule_2
            · unfold is_abs
              simp
            · exact ih_2
        case abs_ e2_x e2_e =>
          unfold bv_small_step at h1
          simp at h1
          rw [← h1]
          apply is_bv_small_step.rule_3
          unfold is_abs
          simp
    case abs_ x e _ =>
      unfold bv_small_step at h1
      simp at h1


def iterate_bv_small_step
  (sub : Symbol_ → Term_ → Term_ → Term_)
  (fuel : Nat)
  (e : Term_) :
  Term_ :=
  if fuel > 0
  then
    match bv_small_step sub e with
    | Option.some next => iterate_bv_small_step sub (fuel - 1) next
    | Option.none => e
  else e


#eval iterate_bv_small_step (fun x y z => sub_single x y z '+') 3 (app_ not_ true_) = false_
#eval iterate_bv_small_step (fun x y z => sub_single x y z '+') 3 (app_ not_ false_) = true_


inductive is_bv_big_step
  (sub : Symbol_ → Term_ → Term_ → Term_) :
  Term_ → Term_ → Prop
| rule_1
  (x : Symbol_) :
  is_bv_big_step sub (Term_.var_ x) (Term_.var_ x)

| rule_2
  (x : Symbol_)
  (e : Term_) :
  is_bv_big_step sub (abs_ x e) (abs_ x e)

| rule_3
  (x : Symbol_)
  (e e' e1 e2 e2' : Term_) :
  is_bv_big_step sub e1 (abs_ x e) →
  is_bv_big_step sub e2 e2' →
  is_bv_big_step sub (sub x e2' e) e' →
  is_bv_big_step sub (app_ e1 e2) e'

| rule_4
  (e1 e1' e2 e2' : Term_) :
  ¬ is_abs e1' →
  is_bv_big_step sub e1 e1' →
  is_bv_big_step sub e2 e2' →
  is_bv_big_step sub (app_ e1 e2) (app_ e1' e2')


example
  (sub : Symbol_ → Term_ → Term_ → Term_)
  (M N : Term_)
  (h1 : Relation.ReflTransGen (is_bv_small_step sub) M N)
  (h2 : is_weak_head_normal_form N) :
  is_bv_big_step sub M N :=
  by
    induction h1
    case refl =>
      induction M
      case var_ x =>
        apply is_bv_big_step.rule_1
      case app_ e1 e2 ih_1 ih_2 =>
        induction e1
        case var_ e1_x =>
          induction e2
          case var_ e2_x =>
            apply is_bv_big_step.rule_4
            · unfold is_abs
              simp
            · apply is_bv_big_step.rule_1
            · apply ih_2
              unfold is_weak_head_normal_form
              simp
          case app_ e2_e1 e2_e2 =>
            apply is_bv_big_step.rule_4
            · unfold is_abs
              simp
            · apply is_bv_big_step.rule_1
            · apply ih_2
              unfold is_weak_head_normal_form
              simp
              sorry
          sorry
        case app_ e1_e1 e1_e2 =>
          apply is_bv_big_step.rule_4
          unfold is_abs
          simp
          sorry
          sorry
        unfold is_weak_head_normal_form at h2
        simp at h2
        unfold is_neutral_weak_head_normal_form at h2
        sorry
      sorry
    sorry
