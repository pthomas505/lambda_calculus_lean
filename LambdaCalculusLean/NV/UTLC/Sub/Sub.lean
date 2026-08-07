import MathlibExtraLean.Fresh
import MathlibExtraLean.FunctionUpdateITE

import TtfpLean.UTLC.Sub.SubIsDef
import TtfpLean.UTLC.Sub.ReplaceFree


set_option linter.style.docString false
set_option linter.style.longLine false
set_option linter.style.emptyLine false


/--
  `sub sigma c M` := The simultaneous replacement of each free occurrence of any variable `x` in the term `M` by `sigma x`. The character `c` is used to generate fresh binding variables as needed to avoid free variable capture.
-/
def sub
  (sigma : String → Term_)
  (c : Char) :
  Term_ → Term_
  | Term_.Var x => sigma x
  | Term_.App P Q => Term_.App (sub sigma c P) (sub sigma c Q)
  | Term_.Abs x P =>
    let x' : String :=
      if ∃ (y : String), y ∈ P.free_var_set \ {x} ∧ x ∈ (sigma y).free_var_set
      then fresh x c ((sub (Function.updateITE sigma x (Term_.Var x)) c P).free_var_set)
      else x
    Term_.Abs x' (sub (Function.updateITE sigma x (Term_.Var x')) c P)


/--
  `sub_single x N M c` := `x -> N` in `M`
-/
def sub_single
  (x : String)
  (N : Term_)
  (M : Term_)
  (c : Char) :
  Term_ :=
  sub (Function.updateITE Term_.Var x N) c M


/--
  `sub_var x y M c` := `x -> y` in `M`
-/
def sub_var
  (x : String)
  (y : String)
  (M : Term_)
  (c : Char) :
  Term_ :=
  sub_single x (Term_.Var y) M c


#eval sub_var "x" "y" (Term_.Abs "x" (Term_.Var "x")) '+'
#eval sub_var "x" "z" (Term_.Abs "y" (Term_.Var "x")) '+'
#eval sub_var "x" "y" (Term_.Abs "y" (Term_.Var "x")) '+'
#eval sub_var "x" "z" (Term_.Var "y") '+'
#eval sub_var "x" "z" (Term_.Var "x") '+'


-- ----------------------------------------------------------------------------


theorem sub_id
  (M : Term_)
  (c : Char) :
  sub Term_.Var c M = M :=
  by
    induction M
    case Var v =>
      unfold sub
      apply Eq.refl
    case App P Q ih_1 ih_2 =>
      unfold sub
      rewrite [ih_1]
      rewrite [ih_2]
      apply Eq.refl
    case Abs v P ih =>
      unfold sub
      simp only [Term_.free_var_set]
      split
      case isTrue c1 =>
        simp only [Finset.mem_sdiff, Finset.mem_singleton] at c1
        obtain ⟨y, ⟨⟨c1_left_left, c1_left_right⟩, c1_right⟩⟩ := c1
        rewrite [c1_right] at c1_left_right
        contradiction
      case isFalse c1 =>
        congr
        simp only [Function.updateITE_same]
        exact ih


theorem sub_single_not_mem
  (x : String)
  (N : Term_)
  (M : Term_)
  (c : Char)
  (h1 : x ∉ M.free_var_set) :
  sub_single x N M c = M :=
  by
    unfold sub_single

    induction M
    case Var v =>
      unfold Term_.free_var_set at h1
      simp only [Finset.mem_singleton] at h1

      unfold sub
      unfold Function.updateITE
      split
      case isTrue c1 =>
        rewrite [c1] at h1
        contradiction
      case isFalse c1 =>
        apply Eq.refl
    case App P Q ih_1 ih_2 =>
      unfold Term_.free_var_set at h1
      simp only [Finset.mem_union] at h1
      rewrite [not_or] at h1
      obtain ⟨h1_left, h1_right⟩ := h1

      unfold sub
      rewrite [ih_1 h1_left]
      rewrite [ih_2 h1_right]
      apply Eq.refl
    case Abs v P ih =>
      unfold Term_.free_var_set at h1
      simp only [Finset.mem_sdiff, Finset.mem_singleton] at h1
      rewrite [not_and'] at h1

      unfold sub
      simp only [Finset.mem_sdiff, Finset.mem_singleton]
      split
      case isTrue c1 =>
        simp only [Finset.mem_sdiff, Finset.mem_singleton] at c1
        obtain ⟨y, ⟨⟨c1_left_left, c1_left_right⟩, c1_right⟩⟩ := c1
        unfold Function.updateITE at c1_right

        split at c1_right
        case isTrue c2 =>
          rewrite [c2] at c1_left_left
          rewrite [c2] at c1_left_right
          specialize h1 c1_left_right
          contradiction
        case isFalse c2 =>
          unfold Term_.free_var_set at c1_right
          simp only [Finset.mem_singleton] at c1_right
          rewrite [c1_right] at c1_left_right
          contradiction
      case isFalse c1 =>
        congr
        by_cases c2 : x = v
        · rewrite [c2]
          rewrite [Function.updateITE_idem]
          rewrite [Function.updateITE_same]
          · apply sub_id
          · apply Eq.refl
        · have s1 : Function.updateITE (Function.updateITE Term_.Var x N) v (Term_.Var v) = Function.updateITE Term_.Var x N :=
          by
            apply Function.updateITE_same
            unfold Function.updateITE
            split
            case isTrue c3 =>
              rewrite [c3] at c2
              contradiction
            case isFalse c3 =>
              apply Eq.refl

          rewrite [s1]
          apply ih
          apply h1
          exact c2


theorem extracted_1
  (x : String)
  (N : Term_)
  (y : String)
  (P : Term_)
  (c : Char)
  (h1 : ¬ x = y)
  (h2 : y ∉ N.free_var_set) :
  sub_single x N (Term_.Abs y P) c =
    Term_.Abs y (sub_single x N P c) :=
  by
    unfold sub_single
    simp only [sub]
    split
    case isTrue c1 =>
      simp only [Finset.mem_sdiff, Finset.mem_singleton] at c1
      obtain ⟨z, ⟨⟨c1_left_left, c1_left_right⟩, c1_right⟩⟩ := c1
      unfold Function.updateITE at c1_right
      split at c1_right
      case isTrue c2 =>
        contradiction
      case isFalse c2 =>
        unfold Term_.free_var_set at c1_right
        simp only [Finset.mem_singleton] at c1_right
        rewrite [c1_right] at c1_left_right
        contradiction
    case isFalse c1 =>
      congr 2
      apply Function.updateITE_same
      unfold Function.updateITE
      split
      case isTrue c2 =>
        rewrite [c2] at h1
        contradiction
      case isFalse c2 =>
        apply Eq.refl


example
  (x : String)
  (N : Term_)
  (M : Term_)
  (c : Char)
  (h1 : sub_is_def_v3_alt x N M) :
  sub_single x N M c = replace_free x N M :=
  by
    induction h1
    case var y =>
      unfold sub_single
      unfold sub
      unfold Function.updateITE
      split
      case isTrue c1 =>
        unfold replace_free
        split
        case isTrue c2 =>
          apply Eq.refl
        case isFalse c2 =>
          rewrite [c1] at c2
          contradiction
      case isFalse c1 =>
      unfold replace_free
      split
      case isTrue c2 =>
        rewrite [c2] at c1
        contradiction
      case isFalse c2 =>
        apply Eq.refl
    case app P Q ih_1 ih_2 ih_3 ih_4 =>
      unfold replace_free
      rewrite [← ih_3]
      rewrite [← ih_4]

      unfold sub_single
      simp only [sub]
    case abs_1 y P ih =>
      rewrite [ih]

      unfold replace_free
      split
      case isTrue c1 =>
        apply sub_single_not_mem
        unfold Term_.free_var_set
        simp only [Finset.mem_sdiff, Finset.mem_singleton]
        rewrite [not_and']
        intro a1
        contradiction
      case isFalse c1 =>
        contradiction
    case abs_2 y P ih_1 ih_2 =>
      unfold replace_free
      split
      case isTrue c1 =>
        contradiction
      case isFalse c1 =>
        have s1 : sub_single x N (Term_.Abs y P) c = Term_.Abs y P :=
        by
          apply sub_single_not_mem
          unfold Term_.free_var_set
          simp only [Finset.mem_sdiff, Finset.mem_singleton]
          rewrite [not_and']
          intro a1
          simp only [← is_free_in_iff_mem_free_var_set]
          exact ih_2

        rewrite [s1]

        rewrite [not_is_free_in_replace_free x N P ih_2]
        apply Eq.refl
    case abs_3 y P ih_1 ih_2 ih_3 ih_4 =>
      unfold replace_free
      split
      case isTrue c1 =>
        contradiction
      case isFalse c1 =>
        rewrite [← ih_4]
        apply extracted_1
        · exact c1
        · simp only [← is_free_in_iff_mem_free_var_set]
          exact ih_2
