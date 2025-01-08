import LC.NV.UTLC.Comb
import LC.NV.UTLC.Reduce.NF
import LC.NV.UTLC.Sub.Sub


set_option autoImplicit false


open Term_


-- Call-by-Name Reduction to Weak Head Normal Form

-- Like normal order, but no reductions are performed inside abstractions. Call-by-name reduction is the weak reduction strategy that reduces the leftmost outermost redex not inside a lambda abstraction.


inductive is_bn_small_step
  (sub : Symbol_ → Term_ → Term_ → Term_) :
  Term_ → Term_ → Prop
| rule_1
  (e1 e1' e2 : Term_) :
  is_bn_small_step sub e1 e1' →
  is_bn_small_step sub (app_ e1 e2) (app_ e1' e2)

| rule_2
  (x : Symbol_)
  (e1 e2 : Term_) :
  is_bn_small_step sub (app_ (abs_ x e1) e2) (sub x e2 e1)


def bn_small_step
  (sub : Symbol_ → Term_ → Term_ → Term_) :
  Term_ → Option Term_

  -- rule_2
| app_ (abs_ x e1) e2 => Option.some (sub x e2 e1)

  -- rule_1
| app_ e1 e2 =>
  match bn_small_step sub e1 with
  | Option.some e1' => app_ e1' e2
  | Option.none => Option.none

| _ => Option.none


example
  (sub : Symbol_ → Term_ → Term_ → Term_)
  (M N : Term_)
  (h1 : is_bn_small_step sub M N) :
  bn_small_step sub M = Option.some N :=
  by
    induction h1
    case rule_1 e1 e1' e2 ih_1 ih_2 =>
      cases e1
      case var_ e1_x =>
        cases ih_1
      case app_ e1_1 e1_2 =>
        unfold bn_small_step
        rw [ih_2]
      case abs_ e1_x e1_e =>
        cases ih_1
    case rule_2 x e1 e2 =>
      unfold bn_small_step
      rfl


example
  (sub : Symbol_ → Term_ → Term_ → Term_)
  (M N : Term_)
  (h1 : bn_small_step sub M = Option.some N) :
  is_bn_small_step sub M N :=
  by
    induction M generalizing N
    case var_ x =>
      unfold bn_small_step at h1
      simp at h1
    case app_ e1 e2 ih_1 _ =>
      cases e1
      case var_ e1_x =>
        cases h1
      case app_ e1_e1 e1_e2 =>
        unfold bn_small_step at h1
        cases h : bn_small_step sub (e1_e1.app_ e1_e2)
        case none =>
          rw [h] at h1
          simp at h1
        case some val =>
          rw [h] at h1
          simp at h1
          specialize ih_1 val h
          rw [← h1]
          exact is_bn_small_step.rule_1 (e1_e1.app_ e1_e2) val e2 ih_1
      case abs_ e1_x e1_e =>
        unfold bn_small_step at h1
        simp at h1
        rw [← h1]
        exact is_bn_small_step.rule_2 e1_x e1_e e2
    case abs_ x e _ =>
      unfold bn_small_step at h1
      simp at h1


def iterate_bn_small_step
  (sub : Symbol_ → Term_ → Term_ → Term_)
  (fuel : Nat)
  (e : Term_) :
  Term_ :=
  if fuel > 0
  then
    match bn_small_step sub e with
    | Option.some next => iterate_bn_small_step sub (fuel - 1) next
    | Option.none => e
  else e


#eval iterate_bn_small_step (fun x y z => sub_single x y z '+') 3 (app_ not_ true_) = false_
#eval iterate_bn_small_step (fun x y z => sub_single x y z '+') 3 (app_ not_ false_) = true_


inductive is_bn_big_step
  (sub : Symbol_ → Term_ → Term_ → Term_) :
  Term_ → Term_ → Prop
| rule_1
  (x : Symbol_) :
  is_bn_big_step sub (Term_.var_ x) (Term_.var_ x)

| rule_2
  (x : Symbol_)
  (e : Term_) :
  is_bn_big_step sub (abs_ x e) (abs_ x e)

| rule_3
  (x : Symbol_)
  (e e' e1 e2 : Term_) :
  is_bn_big_step sub e1 (abs_ x e) →
  is_bn_big_step sub (sub x e2 e) e' →
  is_bn_big_step sub (app_ e1 e2) e'

| rule_4
  (e1 e1' e2 : Term_) :
  ¬ is_abs e1' →
  is_bn_big_step sub e1 e1' →
  is_bn_big_step sub (app_ e1 e2) (app_ e1' e2)


example
  (sub : Symbol_ → Term_ → Term_ → Term_)
  (M N : Term_)
  (h1 : is_bn_big_step sub M N) :
  is_weak_head_normal_form N :=
  by
    induction h1
    case rule_1 x =>
      unfold is_weak_head_normal_form
      simp
    case rule_2 x e =>
      unfold is_weak_head_normal_form
      simp
    case rule_3 _ _ _ _ _ _ _ _ ih_4 =>
      exact ih_4
    case rule_4 e1 e1' e2 ih_1 ih_2 ih_3 =>
      unfold is_weak_head_normal_form
      simp
      cases e1'
      case var_ e1'_x =>
        unfold is_neutral_weak_head_normal_form
        simp only
      case app_ e1'_e1 e1'_e2 =>
        unfold is_weak_head_normal_form at ih_3
        simp at ih_3
        unfold is_neutral_weak_head_normal_form
        exact ih_3
      case abs_ e1'_x e1'_e =>
        unfold is_abs at ih_1
        simp at ih_1


lemma is_bn_small_step_refl_trans_rule_1
  (sub : Symbol_ → Term_ → Term_ → Term_)
  (e1 e1' e2 : Term_)
  (h1 : Relation.ReflTransGen (is_bn_small_step sub) e1 e1') :
  Relation.ReflTransGen (is_bn_small_step sub) (app_ e1 e2) (app_ e1' e2) :=
  by
    induction h1
    case refl =>
      exact Relation.ReflTransGen.refl
    case tail b c _ ih_2 ih_3 =>
      apply Relation.ReflTransGen.trans ih_3
      apply Relation.ReflTransGen.single
      apply is_bn_small_step.rule_1
      exact ih_2


example
  (sub : Symbol_ → Term_ → Term_ → Term_)
  (M N : Term_)
  (h1 : is_bn_big_step sub M N) :
  Relation.ReflTransGen (is_bn_small_step sub) M N :=
  by
    induction h1
    case rule_1 x =>
      exact Relation.ReflTransGen.refl
    case rule_2 x e =>
      exact Relation.ReflTransGen.refl
    case rule_3 x e e' e1 e2 _ _ ih_3 ih_4 =>
      have s1 : Relation.ReflTransGen (is_bn_small_step sub) (e1.app_ e2) (sub x e2 e) :=
      by
        apply Relation.ReflTransGen.trans
        apply is_bn_small_step_refl_trans_rule_1; exact ih_3
        apply Relation.ReflTransGen.single
        apply is_bn_small_step.rule_2
      apply Relation.ReflTransGen.trans s1; exact ih_4
    case rule_4 e1 e1' e2 _ _ ih_3 =>
      apply is_bn_small_step_refl_trans_rule_1; exact ih_3


def bn_big_step_fuel
  (sub : Symbol_ → Term_ → Term_ → Term_)
  (fuel : Nat)
  (e : Term_) :
  Option Term_ :=
  if fuel > 0
  then
    match e with
    | Term_.var_ x => Option.some (Term_.var_ x)
    | abs_ x e => Option.some (abs_ x e)
    | app_ e1 e2 =>
      match bn_big_step_fuel sub fuel e1 with
      | Option.some (abs_ x e) => bn_big_step_fuel sub (fuel - 1) (sub x e2 e)
      | Option.some e1' => app_ e1' e2
      | _ => Option.none
  else Option.none


#eval bn_big_step_fuel (fun x y z => sub_single x y z '+') 3 (app_ not_ true_) = false_
#eval bn_big_step_fuel (fun x y z => sub_single x y z '+') 3 (app_ not_ false_) = true_


example
  (sub : Symbol_ → Term_ → Term_ → Term_)
  (fuel : Nat)
  (n : Nat)
  (M N : Term_)
  (h1 : bn_big_step_fuel sub fuel M = Option.some N) :
  bn_big_step_fuel sub (fuel + n) M = Option.some N :=
  by
    sorry


example
  (sub : Symbol_ → Term_ → Term_ → Term_)
  (M N : Term_)
  (h1 : is_bn_big_step sub M N) :
  ∃ (fuel : Nat), fuel > 0 ∧ bn_big_step_fuel sub fuel M = Option.some N :=
  by
    induction h1
    case rule_1 x =>
      simp only [bn_big_step_fuel]
      simp
      apply Exists.intro 1
      simp
    case rule_2 x e =>
      simp only [bn_big_step_fuel]
      simp
      apply Exists.intro 1
      simp
    all_goals
      sorry


example
  (sub : Symbol_ → Term_ → Term_ → Term_)
  (fuel : Nat)
  (M N : Term_)
  (h1 : bn_big_step_fuel sub fuel M = Option.some N) :
  is_bn_big_step sub M N :=
  by
    induction M generalizing N fuel
    case var_ x =>
      unfold bn_big_step_fuel at h1
      simp at h1
      obtain ⟨h1_left, h1_right⟩ := h1
      rw [← h1_right]
      apply is_bn_big_step.rule_1
    case app_ e1 e2 ih_1 ih_2 =>
      cases c1 : bn_big_step_fuel sub fuel e1
      case none =>
        simp only [bn_big_step_fuel] at h1
        rw [c1] at h1
        simp at h1
      case some val =>
        simp only [bn_big_step_fuel] at h1
        rw [c1] at h1
        cases val
        case var_ x' =>
          simp at h1
          obtain ⟨h1_left, h1_right⟩ := h1
          rw [← h1_right]
          apply is_bn_big_step.rule_4
          · simp only [is_abs]
            simp
          · exact ih_1 fuel (Term_.var_ x') c1
        case app_ e1' e2' =>
          simp at h1
          obtain ⟨h1_left, h1_right⟩ := h1
          rw [← h1_right]
          apply is_bn_big_step.rule_4
          · simp only [is_abs]
            simp
          · exact ih_1 fuel (app_ e1' e2') c1
        case abs_ x' e' =>
          simp at h1
          obtain ⟨h1_left, h1_right⟩ := h1
          apply is_bn_big_step.rule_3 x' e'
          · exact ih_1 fuel (abs_ x' e') c1
          · sorry
    case abs_ x e ih =>
      unfold bn_big_step_fuel at h1
      simp at h1
      obtain ⟨h1_left, h1_right⟩ := h1
      rw [← h1_right]
      apply is_bn_big_step.rule_2
