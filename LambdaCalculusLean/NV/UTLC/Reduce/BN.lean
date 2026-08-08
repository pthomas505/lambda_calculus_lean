import LambdaCalculusLean.NV.UTLC.Comb
import LambdaCalculusLean.NV.UTLC.Reduce.NF
import LambdaCalculusLean.NV.UTLC.Sub.Sub


set_option linter.style.longLine false
set_option linter.style.emptyLine false


-- Call-by-Name Reduction to Weak Head Normal Form

-- Like normal order, but no reductions are performed inside abstractions. Call-by-name reduction is the weak reduction strategy that reduces the leftmost outermost redex not inside a lambda abstraction.


inductive is_bn_small_step
  (sub : String → Term_ → Term_ → Term_) :
  Term_ → Term_ → Prop
| rule_1
  (e1 e1' e2 : Term_) :
  is_bn_small_step sub e1 e1' →
  is_bn_small_step sub (Term_.App e1 e2) (Term_.App e1' e2)

| rule_2
  (x : String)
  (e1 e2 : Term_) :
  is_bn_small_step sub (Term_.App (Term_.Abs x e1) e2) (sub x e2 e1)


def bn_small_step
  (sub : String → Term_ → Term_ → Term_) :
  Term_ → Option Term_

  -- rule_2
| Term_.App (Term_.Abs x e1) e2 => Option.some (sub x e2 e1)

  -- rule_1
| Term_.App e1 e2 =>
  match bn_small_step sub e1 with
  | Option.some e1' => Term_.App e1' e2
  | Option.none => Option.none

| _ => Option.none


example
  (sub : String → Term_ → Term_ → Term_)
  (M N : Term_)
  (h1 : is_bn_small_step sub M N) :
  bn_small_step sub M = Option.some N :=
  by
    induction h1
    case rule_1 e1 e1' e2 ih_1 ih_2 =>
      cases e1
      case Var e1_x =>
        cases ih_1
      case App e1_1 e1_2 =>
        unfold bn_small_step
        rewrite [ih_2]
        simp only
      case Abs e1_x e1_e =>
        cases ih_1
    case rule_2 x e1 e2 =>
      unfold bn_small_step
      apply Eq.refl


example
  (sub : String → Term_ → Term_ → Term_)
  (M N : Term_)
  (h1 : bn_small_step sub M = Option.some N) :
  is_bn_small_step sub M N :=
  by
    induction M generalizing N
    case Var x =>
      unfold bn_small_step at h1
      contradiction
    case App e1 e2 ih_1 ih_2 =>
      cases e1
      case Var e1_x =>
        cases h1
      case App e1_e1 e1_e2 =>
        unfold bn_small_step at h1
        cases h : bn_small_step sub (e1_e1.App e1_e2)
        case none =>
          rewrite [h] at h1
          simp only at h1
          contradiction
        case some val =>
          rewrite [h] at h1
          simp only [Option.some.injEq] at h1
          specialize ih_1 val h
          rw [← h1]
          exact is_bn_small_step.rule_1 (e1_e1.App e1_e2) val e2 ih_1
      case Abs e1_x e1_e =>
        unfold bn_small_step at h1
        simp only [Option.some.injEq] at h1
        rewrite [← h1]
        exact is_bn_small_step.rule_2 e1_x e1_e e2
    case Abs x e _ =>
      unfold bn_small_step at h1
      contradiction


def iterate_bn_small_step
  (sub : String → Term_ → Term_ → Term_)
  (fuel : Nat)
  (e : Term_) :
  Term_ :=
  if fuel > 0
  then
    match bn_small_step sub e with
    | Option.some next => iterate_bn_small_step sub (fuel - 1) next
    | Option.none => e
  else e


#eval iterate_bn_small_step (fun x y z => sub_single x y z '+') 3 (Term_.App not_ true_) = false_
#eval iterate_bn_small_step (fun x y z => sub_single x y z '+') 3 (Term_.App not_ false_) = true_


inductive is_bn_big_step
  (sub : String → Term_ → Term_ → Term_) :
  Term_ → Term_ → Prop
| rule_1
  (x : String) :
  is_bn_big_step sub (Term_.Var x) (Term_.Var x)

| rule_2
  (x : String)
  (e : Term_) :
  is_bn_big_step sub (Term_.Abs x e) (Term_.Abs x e)

| rule_3
  (x : String)
  (e e' e1 e2 : Term_) :
  is_bn_big_step sub e1 (Term_.Abs x e) →
  is_bn_big_step sub (sub x e2 e) e' →
  is_bn_big_step sub (Term_.App e1 e2) e'

| rule_4
  (e1 e1' e2 : Term_) :
  ¬ Term_.is_abs e1' →
  is_bn_big_step sub e1 e1' →
  is_bn_big_step sub (Term_.App e1 e2) (Term_.App e1' e2)


example
  (sub : String → Term_ → Term_ → Term_)
  (M N : Term_)
  (h1 : is_bn_big_step sub M N) :
  is_weak_head_normal_form N :=
  by
    induction h1
    case rule_1 x =>
      simp only [is_weak_head_normal_form]
    case rule_2 x e =>
      simp only [is_weak_head_normal_form]
    case rule_3 _ _ _ _ _ _ _ _ ih_4 =>
      exact ih_4
    case rule_4 e1 e1' e2 ih_1 ih_2 ih_3 =>
      simp only [is_weak_head_normal_form]
      cases e1'
      case Var e1'_x =>
        simp only [is_neutral_weak_head_normal_form]
      case App e1'_e1 e1'_e2 =>
        simp only [is_weak_head_normal_form] at ih_3
        unfold is_neutral_weak_head_normal_form
        exact ih_3
      case Abs e1'_x e1'_e =>
        simp only [Term_.is_abs] at ih_1
        contradiction


lemma is_bn_small_step_refl_trans_rule_1
  (sub : String → Term_ → Term_ → Term_)
  (e1 e1' e2 : Term_)
  (h1 : Relation.ReflTransGen (is_bn_small_step sub) e1 e1') :
  Relation.ReflTransGen (is_bn_small_step sub) (Term_.App e1 e2) (Term_.App e1' e2) :=
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
  (sub : String → Term_ → Term_ → Term_)
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
      have s1 : Relation.ReflTransGen (is_bn_small_step sub) (e1.App e2) (sub x e2 e) :=
      by
        apply Relation.ReflTransGen.trans
        · apply is_bn_small_step_refl_trans_rule_1
          exact ih_3
        · apply Relation.ReflTransGen.single
          apply is_bn_small_step.rule_2
      apply Relation.ReflTransGen.trans s1
      exact ih_4
    case rule_4 e1 e1' e2 _ _ ih_3 =>
      apply is_bn_small_step_refl_trans_rule_1
      exact ih_3


def bn_big_step_fuel
  (sub : String → Term_ → Term_ → Term_)
  (fuel : Nat)
  (e : Term_) :
  Option Term_ :=
  if fuel > 0
  then
    match e with
    | Term_.Var x => Option.some (Term_.Var x)
    | Term_.Abs x e => Option.some (Term_.Abs x e)
    | Term_.App e1 e2 =>
      match bn_big_step_fuel sub fuel e1 with
      | Option.some (Term_.Abs x e) => bn_big_step_fuel sub (fuel - 1) (sub x e2 e)
      | Option.some e1' => Term_.App e1' e2
      | _ => Option.none
  else Option.none


#eval bn_big_step_fuel (fun x y z => sub_single x y z '+') 3 (Term_.App not_ true_) = false_
#eval bn_big_step_fuel (fun x y z => sub_single x y z '+') 3 (Term_.App not_ false_) = true_


example
  (sub : String → Term_ → Term_ → Term_)
  (fuel : Nat)
  (n : Nat)
  (M N : Term_)
  (h1 : bn_big_step_fuel sub fuel M = Option.some N) :
  bn_big_step_fuel sub (fuel + n) M = Option.some N :=
  by
    sorry


example
  (sub : String → Term_ → Term_ → Term_)
  (M N : Term_)
  (h1 : is_bn_big_step sub M N) :
  ∃ (fuel : Nat), fuel > 0 ∧ bn_big_step_fuel sub fuel M = Option.some N :=
  by
    induction h1
    case rule_1 x =>
      apply Exists.intro 1
      simp only [bn_big_step_fuel]
      split
      case isTrue c1 =>
        constructor
        · exact Nat.one_pos
        · apply Eq.refl
      case isFalse c1 =>
        exfalso
        apply c1
        exact Nat.one_pos
    case rule_2 x e =>
      apply Exists.intro 1
      simp only [bn_big_step_fuel]
      split
      case isTrue c1 =>
        constructor
        · exact c1
        · apply Eq.refl
      case isFalse c1 =>
        exfalso
        apply c1
        exact Nat.one_pos
    all_goals
      sorry


example
  (sub : String → Term_ → Term_ → Term_)
  (fuel : Nat)
  (M N : Term_)
  (h1 : bn_big_step_fuel sub fuel M = Option.some N) :
  is_bn_big_step sub M N :=
  by
    induction M generalizing N fuel
    case Var x =>
      simp only [bn_big_step_fuel] at h1
      split at h1
      case isTrue c1 =>
        cases h1
        apply is_bn_big_step.rule_1
      case isFalse c1 =>
        contradiction
    case App e1 e2 ih_1 ih_2 =>
      cases c1 : bn_big_step_fuel sub fuel e1
      case none =>
        simp only [bn_big_step_fuel] at h1
        rewrite [c1] at h1
        simp only at h1
        split at h1
        case isTrue c2 =>
          contradiction
        case isFalse c2 =>
          contradiction
      case some val =>
        simp only [bn_big_step_fuel] at h1
        rewrite [c1] at h1
        split at h1
        case isTrue c2 =>
          cases val
          case Var x' =>
            simp only at h1
            simp only [Option.some.injEq] at h1
            rewrite [← h1]
            apply is_bn_big_step.rule_4
            · simp only [Term_.is_abs]
              intro contra
              contradiction
            · exact ih_1 fuel (Term_.Var x') c1
          case App e1' e2' =>
            simp only [Option.some.injEq] at h1
            rewrite [← h1]
            apply is_bn_big_step.rule_4
            · simp only [Term_.is_abs]
              intro contra
              contradiction
            · exact ih_1 fuel (Term_.App e1' e2') c1
          case Abs x' e' =>
            simp only at h1
            apply is_bn_big_step.rule_3 x' e'
            · exact ih_1 fuel (Term_.Abs x' e') c1
            · sorry
        case isFalse c2 =>
          contradiction
    case Abs x e ih =>
      simp only [bn_big_step_fuel] at h1
      split at h1
      case isTrue c1 =>
        simp only [Option.some.injEq] at h1
        rewrite [← h1]
        apply is_bn_big_step.rule_2
      case isFalse c1 =>
        contradiction
