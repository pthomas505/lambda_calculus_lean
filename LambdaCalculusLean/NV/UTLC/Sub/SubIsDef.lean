import LC.NV.UTLC.Sub.ReplaceFree


set_option autoImplicit false


open Term_


/--
  `sub_is_def_v3 M x N` := True if and only if `M [ x := N ]` is defined
-/
inductive sub_is_def_v3 : Term_ → Symbol_ → Term_ → Prop

-- y [ x := N ] is defined
| var
  (y : Symbol_)
  (x : Symbol_)
  (N : Term_) :
  sub_is_def_v3 (var_ y) x N

-- P [ x := N ] is defined → Q [ x := N ] is defined → (P Q) [ x := N ] is defined
| app
  (P : Term_)
  (Q : Term_)
  (x : Symbol_)
  (N : Term_) :
  sub_is_def_v3 P x N →
  sub_is_def_v3 Q x N →
  sub_is_def_v3 (app_ P Q) x N

-- x = y → ( λ y . P ) [ x := N ] is defined
| abs_1
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_) :
  x = y →
  sub_is_def_v3 (abs_ y P) x N

| abs_2
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_) :
  ¬ x = y →
  x ∉ P.free_var_set →
  sub_is_def_v3 (abs_ y P) x N

| abs_3
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_) :
  ¬ x = y →
  y ∉ N.free_var_set →
  sub_is_def_v3 P x N →
  sub_is_def_v3 (abs_ y P) x N


-------------------------------------------------------------------------------


-- [1]
lemma lemma_1_2_5_i_a
  (M : Term_)
  (x : Symbol_)
  (N : Term_)
  (h1 : x ∉ M.free_var_set) :
  sub_is_def_v3 M x N :=
  by
    induction M
    case var_ x_ =>
      exact sub_is_def_v3.var x_ x N

    case app_ P_ Q_ ih_1 ih_2 =>
      unfold Term_.free_var_set at h1
      simp at h1
      obtain ⟨h1_left, h1_right⟩ := h1
      specialize ih_1 h1_left
      specialize ih_2 h1_right
      exact sub_is_def_v3.app P_ Q_ x N ih_1 ih_2

    case abs_ x_ P_ _ =>
      by_cases c1 : x = x_
      · exact sub_is_def_v3.abs_1 x_ P_ x N c1
      · apply sub_is_def_v3.abs_2 x_ P_ x N c1
        unfold free_var_set at h1
        simp at h1
        tauto


-- [1]
lemma lemma_1_2_5_ii
  (M : Term_)
  (x : Symbol_)
  (N : Term_)
  (y : Symbol_)
  (h1 : sub_is_def_v3 M x N) :
  y ∈ (replace_free x N M).free_var_set ↔
    (y ∈ M.free_var_set ∧ ¬ x = y) ∨ (y ∈ N.free_var_set ∧ x ∈ M.free_var_set) :=
  by
    induction h1
    case var y_ x_ N_ =>
      unfold replace_free
      split_ifs
      case pos c1 =>
        simp only [free_var_set]
        simp
        rw [c1]
        tauto
      case neg c1 =>
        simp only [free_var_set]
        simp
        constructor
        · intro a1
          rw [a1]
          tauto
        · intro a1
          tauto
    case app P_ Q_ x_ N_ ih_1 ih_2 ih_3 ih_4 =>
      unfold replace_free
      simp only [free_var_set]
      simp
      tauto
    case abs_1 y_ P_ x_ N_ ih =>
      unfold replace_free
      split_ifs
      simp only [free_var_set]
      simp
      rw [ih]
      tauto
    case abs_2 y_ P_ x_ N_ ih_1 ih_2 =>
      unfold replace_free
      split_ifs
      simp only [free_var_set]
      simp

      have s1 : replace_free x_ N_ P_ = P_ := by apply replace_free_not_mem; exact ih_2
      rw [s1]

      constructor
      · intro a1
        obtain ⟨a1_left, a1_right⟩ := a1

        have s1 : ¬ x_ = y :=
        by
          intro contra
          apply ih_2
          rw [contra]
          exact a1_left

        tauto
      · tauto
    case abs_3 y_ P_ x_ N_ ih_1 ih_2 ih_3 ih_4 =>
      unfold replace_free
      split_ifs
      simp only [free_var_set]
      simp

      constructor
      · intro a1
        tauto
      · intro a1
        cases a1
        case _ c1 =>
          tauto
        case _ c2 =>
          constructor
          · rw [ih_4]
            tauto
          · intro contra
            apply ih_2
            rw [contra] at c2
            tauto


-- [1]
lemma lemma_1_2_5_iii_a
  (M : Term_)
  (x : Symbol_) :
  sub_is_def_v3 M x (var_ x) :=
  by
    induction M
    case var_ x_ =>
      apply sub_is_def_v3.var
    case app_ P_ Q_ ih_1 ih_2 =>
      apply sub_is_def_v3.app
      · exact ih_1
      · exact ih_2
    case abs_ x_ P_ ih =>
      by_cases c1 : x = x_
      case pos =>
        rw [c1]
        apply sub_is_def_v3.abs_1
        rfl
      case neg =>
        apply sub_is_def_v3.abs_3
        · exact c1
        · unfold free_var_set
          simp
          intro contra
          apply c1
          rw [contra]
        · exact ih


-- [1]
lemma lemma_1_2_6_a_left
  (M N L : Term_)
  (x y : Symbol_)
  (h1 : sub_is_def_v3 M x N)
  (h2 : sub_is_def_v3 (replace_free x N M) y L)
  (h3 : ¬ x = y)
  (h4 : x ∉ L.free_var_set ∨ y ∉ M.free_var_set) :
  sub_is_def_v3 M y L :=
  by
    induction M
    case var_ x_ =>
      apply sub_is_def_v3.var
    case app_ P_ Q_ ih_1 ih_2 =>
      cases h1
      case app h1_left h1_right =>
        unfold replace_free at h2
        cases h2
        case app h3_left h3_right =>
          simp only [free_var_set] at h4
          simp at h4
          apply sub_is_def_v3.app
          · tauto
          · tauto
    case abs_ x_ P_ ih =>
      cases h1
      case abs_1 c1 =>
        unfold replace_free at h2
        split_ifs at h2
        exact h2
      case abs_2 c1 c2 =>
        unfold replace_free at h2
        split_ifs at h2

        have s1 : replace_free x N P_ = P_ := by apply replace_free_not_mem; exact c2
        rw [s1] at h2
        exact h2
      case abs_3 c1 c2 c3 =>
        unfold replace_free at h2
        split_ifs at h2

        simp only [free_var_set] at h4
        simp at h4

        cases h2
        case abs_1 c4 =>
          apply sub_is_def_v3.abs_1
          exact c4
        case abs_2 c4 c5 =>
          apply sub_is_def_v3.abs_2
          · exact c4
          · intro contra
            apply c5
            exact replace_free_mem_free_var_set P_ x N y contra h3
        case abs_3 c4 c5 c6 =>
          apply sub_is_def_v3.abs_3
          · exact c4
          · exact c5
          · apply ih c3 c6
            tauto


-- [1]
lemma lemma_1_2_6_a_right
  (M N L : Term_)
  (x y : Symbol_)
  (h1 : sub_is_def_v3 M x N)
  (h2 : sub_is_def_v3 (replace_free x N M) y L)
  (h3 : ¬ x = y)
  (h4 : x ∉ L.free_var_set ∨ y ∉ M.free_var_set) :
  sub_is_def_v3 (replace_free y L M) x (replace_free y L N) :=
  by
    induction M
    case var_ x_ =>
      simp only [free_var_set] at h4
      simp at h4

      cases h4
      case inl h5_left =>
        simp only [replace_free]
        split_ifs
        case pos c1 =>
          exact lemma_1_2_5_i_a L x (replace_free y L N) h5_left
        case neg c1 =>
          exact sub_is_def_v3.var x_ x (replace_free y L N)
      case inr h5_right =>
        simp only [replace_free]
        split_ifs
        exact sub_is_def_v3.var x_ x (replace_free y L N)
    case app_ P_ Q_ ih_1 ih_2 =>
      cases h1
      case app c1 c2 =>
        cases h2
        case app c3 c4 =>
          simp only [free_var_set] at h4
          simp at h4

          apply sub_is_def_v3.app
          · tauto
          · tauto
    case abs_ x_ P_ ih =>
      simp only [free_var_set] at h4
      simp at h4

      cases h1
      case abs_1 c1 =>
        simp only [replace_free]
        split_ifs
        case pos c2 =>
          apply sub_is_def_v3.abs_1
          exact c1
        case neg c2 =>
          apply sub_is_def_v3.abs_1
          exact c1
      case abs_2 c1 c2 =>
        simp only [replace_free] at h2
        split_ifs at h2

        simp only [replace_free]
        split_ifs
        case pos c3 =>
          apply sub_is_def_v3.abs_2
          · exact c1
          · exact c2
        case neg c3 =>
          apply sub_is_def_v3.abs_2
          · exact c1
          · cases h4
            case _ h4_left =>
              apply replace_free_not_mem_either_free_var_set; exact c2; exact h4_left
            case _ h4_right =>
              simp only [free_var_set] at h4_right
              have s1 : y ∉ P_.free_var_set := by tauto
              have s2 : replace_free y L P_ = P_ := replace_free_not_mem P_ y L s1
              rw [s2]
              exact c2
      case abs_3 c1 c2 c3 =>
        simp only [replace_free] at h2
        split_ifs at h2

        cases h2
        case abs_1 c4 =>
          have s1 : replace_free y L (abs_ x_ P_) = abs_ x_ P_ :=
          by
            apply replace_free_not_mem (abs_ x_ P_) y L
            unfold free_var_set
            simp
            intro a1
            exact c4
          rw [s1]

          have s2 : replace_free y L N = N :=
          by
            rw [c4]
            exact replace_free_not_mem N x_ L c2
          rw [s2]

          apply sub_is_def_v3.abs_3; exact c1; exact c2; exact c3;
        case abs_2 c4 c5 =>
          obtain s1 := lemma_1_2_5_ii P_ x N y c3
          rw [s1] at c5
          clear s1
          simp at c5
          obtain ⟨c5_left, c5_right⟩ := c5
          have s2 : y ∉ P_.free_var_set := by tauto
          have s3 : replace_free y L (abs_ x_ P_) = abs_ x_ P_ :=
          by
            apply replace_free_not_mem (abs_ x_ P_) y L
            unfold free_var_set
            simp
            intro a1
            contradiction
          rw [s3]
          by_cases c6 : y ∈ N.free_var_set
          case pos =>
            apply sub_is_def_v3.abs_2
            · exact c1
            · exact c5_right c6
          case neg =>
            have s4 : replace_free y L N = N := replace_free_not_mem N y L c6
            rw [s4]
            exact sub_is_def_v3.abs_3 x_ P_ x N c1 c2 c3
        case abs_3 c4 c5 c6 =>
          simp only [replace_free]
          split_ifs
          apply sub_is_def_v3.abs_3
          · exact c1
          · exact replace_free_not_mem_either_free_var_set N y L x_ c2 c5
          · apply ih
            · exact c3
            · exact c6
            · tauto


-- [1]
lemma lemma_1_2_6_b
  (M N L : Term_)
  (x y : Symbol_)
  (h1 : sub_is_def_v3 M x N)
  (h2 : ¬ x = y)
  (h3 : x ∉ L.free_var_set ∨ y ∉ M.free_var_set) :
  replace_free y L (replace_free x N M) =
    replace_free x (replace_free y L N) (replace_free y L M) :=
  by
    induction M
    case var_ x_ =>
      simp only [replace_free]
      split_ifs
      case pos c1 c2 =>
        rw [c1] at h2
        rw [c2] at h2
        contradiction
      case neg c1 c2 =>
        rw [c1]
        simp only [replace_free]
        simp
      case pos c1 c2 =>
        simp only [free_var_set] at h3
        simp at h3

        have s1 : x ∉ L.free_var_set := by tauto

        rw [c2]
        rw [replace_free]
        simp

        symm
        exact replace_free_not_mem L x (replace_free x_ L N) s1
      case neg c1 c2 =>
        simp only [replace_free]
        split_ifs
        rfl
    case app_ P Q ih_1 ih_2 =>
      simp only [free_var_set] at h3
      simp at h3

      cases h1
      case _ c1 c2 =>
        simp only [replace_free]
        congr 1
        · apply ih_1
          · tauto
          · tauto
        · apply ih_2
          · tauto
          · tauto
    case abs_ x_ P_ ih =>
      simp only [replace_free]
      split_ifs
      case pos c1 c2 =>
        simp only [replace_free]
        split_ifs
        rfl
      case neg c1 c2 =>
        simp only [replace_free]
        split_ifs
        rfl
      case pos c1 c2 =>
        simp only [replace_free]
        split_ifs
        congr 1
        rw [c2]

        cases h1
        case _ c3 =>
          contradiction
        case _ c3 c4 =>
          rw [replace_free_not_mem P_ x N c4]
          rw [replace_free_not_mem P_ x (replace_free x_ L N) c4]
        case _ c3 c4 c5 =>
          rw [replace_free_not_mem N x_ L c4]
      case neg c1 c2 =>
        simp only [replace_free]
        split_ifs
        congr 1
        apply ih
        · cases h1
          case _ c3 =>
            contradiction
          case _ c3 c4 =>
            exact lemma_1_2_5_i_a P_ x N c4
          case _ c3 c4 c5 =>
            exact c5
        · simp only [free_var_set] at h3
          simp at h3
          tauto


-- [1]
lemma lemma_1_2_7_a
  (M : Term_)
  (x y : Symbol_)
  (h1 : sub_is_def_v3 M x (var_ y))
  (h2 : y ∉ M.free_var_set) :
  sub_is_def_v3 (replace_free x (var_ y) M) y (var_ x) :=
  by
    induction M
    case var_ x_ =>
      unfold free_var_set at h2
      simp at h2

      unfold replace_free
      split_ifs
      case pos c1 =>
        apply sub_is_def_v3.var
      case neg c1 =>
        apply sub_is_def_v3.var
    case app_ P_ Q_ ih_1 ih_2 =>
      cases h1
      case app c1 c2 =>
        unfold free_var_set at h2
        simp at h2

        unfold replace_free
        apply sub_is_def_v3.app
        · tauto
        · tauto
    case abs_ x_ P_ ih =>
      unfold free_var_set at h2
      simp at h2

      simp only [replace_free]
      split_ifs
      case pos c1 =>
        by_cases c2 : y = x
        case pos =>
          apply sub_is_def_v3.abs_1
          rw [c1] at c2
          exact c2
        case neg =>
          rw [c1] at c2
          have s1 : y ∉ P_.free_var_set := by tauto
          rw [c1]
          exact sub_is_def_v3.abs_2 x_ P_ y (var_ x_) c2 s1
      case neg c1 =>
        by_cases c2 : y = x_
        case pos =>
          rw [c2]
          exact sub_is_def_v3.abs_1 x_ (replace_free x (var_ x_) P_) x_ (var_ x) rfl
        case neg =>
          apply sub_is_def_v3.abs_3
          · exact c2
          · unfold free_var_set
            simp
            intro contra
            apply c1
            rw [contra]
          · apply ih
            · cases h1
              case _ c3 =>
                contradiction
              case _ c3 c4 =>
                exact lemma_1_2_5_i_a P_ x (var_ y) c4
              case _ c3 c4 c5 =>
                exact c5
            · tauto


-- [1]
lemma lemma_1_2_7_b
  (M : Term_)
  (x y : Symbol_)
  (h1 : sub_is_def_v3 M x (var_ y))
  (h2 : y ∉ M.free_var_set) :
  replace_free y (var_ x) (replace_free x (var_ y) M) = M :=
  by
    by_cases c1 : x = y
    case pos =>
      rw [c1]
      simp only [replace_free_id]
    case neg =>
      obtain s1 := lemma_1_2_6_b M (var_ y) (var_ x) x y h1 c1

      have s2 : replace_free y (var_ x) M = M := replace_free_not_mem M y (var_ x) h2
      rw [s2] at s1
      clear s2

      simp only [replace_free] at s1
      simp at s1

      rw [replace_free_id] at s1

      apply s1
      right
      exact h2


#lint
