import LambdaCalculusLean.NV.UTLC.Sub.IsSub


set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.style.longLine false


-- [1]

theorem lemma_1_2_5_ii_left
  (M : Term_)
  (x : String)
  (N : Term_)
  (y : String)
  (h1 : is_free_in y (replace_free x N M)) :
    ((is_free_in y M ∧ ¬ x = y) ∨
      (is_free_in y N ∧ is_free_in x M)) :=
  by
  by_cases c1 : x = y
  · rewrite [c1] at h1
    rewrite [c1]
    right
    constructor
    · exact is_free_in_replace_free_eq_2 y N M h1
    · exact is_free_in_replace_free_eq_1 y N M h1
  · by_cases c2 : is_free_in y M
    · left
      constructor
      · exact c2
      · exact c1
    · right
      constructor
      · exact is_free_in_replace_free_ne_2 x N M y h1 c2
      · exact is_free_in_replace_free_ne_3 x N M y h1 c2


theorem lemma_1_2_5_ii_right
  (M : Term_)
  (x : String)
  (N : Term_)
  (y : String)
  (h1 : sub_is_def_v3_alt x N M)
  (h2 : (is_free_in y M ∧ ¬ x = y) ∨ (is_free_in y N ∧ is_free_in x M)) :
  is_free_in y (replace_free x N M) :=
  by
  cases h2
  case inl h2 =>
    obtain ⟨h2_left, h2_right⟩ := h2

    apply is_free_in_replace_free_ne_1
    · intro contra
      apply h2_right
      rewrite [contra]
      apply Eq.refl
    · tauto
  case inr h2 =>
    by_cases c1 : y = x
    case pos =>
      rewrite [c1] at h2
      obtain ⟨h2_left, h2_right⟩ := h2

      rewrite [c1]
      exact is_free_in_replace_free_eq_3 x N M h2_left h2_right
    case neg =>
      obtain ⟨h2_left, h2_right⟩ := h2

      exact sub_is_def_is_free_in_replace_free x N M y h2_left h2_right h1


theorem lemma_1_2_5_ii
  (M : Term_)
  (x : String)
  (N : Term_)
  (y : String)
  (h1 : sub_is_def_v3_alt x N M) :
  is_free_in y (replace_free x N M) ↔
    ((is_free_in y M ∧ ¬ x = y) ∨
      (is_free_in y N ∧ is_free_in x M)) :=
  by
    constructor
    · apply lemma_1_2_5_ii_left
    · apply lemma_1_2_5_ii_right
      exact h1


-- ----------------------------------------------------------------------------


theorem lemma_1_2_6_a_1
  (M N L : Term_)
  (x y : String)
  (h1 : sub_is_def_v3_alt x N M)
  (h2 : sub_is_def_v3_alt y L N)
  (h2 : sub_is_def_v3_alt y L (replace_free x N M))
  (h3 : ¬ x = y)
  (h4 : ¬ is_free_in x L ∨ ¬ is_free_in y M) :
  sub_is_def_v3_alt y L M :=
  by
  sorry


theorem lemma_1_2_6_a_right
  (M N L : Term_)
  (x y : String)
  (h1 : sub_is_def_v3_alt x N M)
  (h2 : sub_is_def_v3_alt y L (replace_free x N M))
  (h3 : ¬ x = y)
  (h4 : ¬ is_free_in x L ∨ ¬ is_free_in y M) :
  sub_is_def_v3_alt x (replace_free y L N) (replace_free y L M) :=
  by
    induction M
    case Var v =>
      simp only [is_free_in] at h4

      cases h4
      case inl h4 =>
        simp only [replace_free]
        split
        case isTrue c1 =>
          apply not_is_free_in_sub_is_def
          exact h4
        case isFalse c1 =>
          apply sub_is_def_v3_alt.var
      case inr h4 =>
        simp only [replace_free]
        split
        case isTrue c1 =>
          contradiction
        case isFalse c1 =>
          apply sub_is_def_v3_alt.var
    case App P Q ih_1 ih_2 =>
      cases h1
      case app c1 c2 =>
        cases h2
        case app c3 c4 =>
          simp only [is_free_in] at h4
          rewrite [not_or] at h4

          apply sub_is_def_v3_alt.app
          · tauto
          · tauto
    case Abs v P ih =>
      simp only [is_free_in] at h4
      rewrite [not_and] at h4

      cases h1
      case abs_1 c1 =>
        simp only [replace_free]
        split
        case isTrue c2 =>
          apply sub_is_def_v3_alt.abs_1
          exact c1
        case isFalse c2 =>
          apply sub_is_def_v3_alt.abs_1
          exact c1
      case abs_2 c1 c2 =>
        simp only [replace_free] at h2
        split at h2
        case isTrue c3 =>
          contradiction
        case isFalse c3 =>
          simp only [replace_free]
          split
          case isTrue c4 =>
            apply sub_is_def_v3_alt.abs_2
            · exact c1
            · exact c2
          case isFalse c4 =>
            apply sub_is_def_v3_alt.abs_2
            · exact c1
            · cases h4
              case inl h4 =>
                intro contra
                apply h4
                exact is_free_in_replace_free_ne_2 y L P x contra c2
              case inr h4 =>
                have s2 : replace_free y L P = P :=
                by
                  apply not_is_free_in_replace_free
                  exact h4 c4
                rewrite [s2]
                exact c2
      case abs_3 c1 c2 c3 =>
        simp only [replace_free] at h2
        split at h2
        case isTrue c4 =>
          contradiction
        case isFalse c4 =>
          cases h2
          case abs_1 c5 =>
            rewrite [c5]

            have s1 : replace_free v L N = N :=
            by
              apply not_is_free_in_replace_free
              exact c2
            rewrite [s1]

            have s2 : replace_free v L (Term_.Abs v P) = Term_.Abs v P :=
            by
              apply not_is_free_in_replace_free
              unfold is_free_in
              rewrite [not_and]
              intro contra
              contradiction
            rewrite [s2]

            apply sub_is_def_v3_alt.abs_3
            · exact c1
            · exact c2
            · exact c3
          case abs_2 c5 c6 =>
            obtain s1 := lemma_1_2_5_ii P x N y c3
            rewrite [s1] at c6

            rewrite [not_or] at c6
            simp only [not_and'] at c6
            obtain ⟨c6_left, c6_right⟩ := c6

            have s2 : replace_free y L (Term_.Abs v P) = Term_.Abs v P :=
            by
              apply not_is_free_in_replace_free
              unfold is_free_in
              rewrite [not_and]
              intro a1
              apply c6_left
              exact h3
            rewrite [s2]

            by_cases c7 : is_free_in y N
            · apply sub_is_def_v3_alt.abs_2
              · exact c1
              · intro contra
                apply c6_right
                · exact contra
                · exact c7
            · have s3 : replace_free y L N = N :=
              by
                apply not_is_free_in_replace_free
                exact c7
              rewrite [s3]

              apply sub_is_def_v3_alt.abs_3
              · exact c1
              · exact c2
              · exact c3
          case abs_3 c5 c6 c7 =>
            simp only [replace_free]
            split
            case isTrue c8 =>
              contradiction
            case isFalse c8 =>
              apply sub_is_def_v3_alt.abs_3
              · exact c1
              · intro contra
                apply c6
                exact is_free_in_replace_free_ne_2 y L N v contra c2
              · apply ih
                · exact c3
                · exact c7
                · tauto
