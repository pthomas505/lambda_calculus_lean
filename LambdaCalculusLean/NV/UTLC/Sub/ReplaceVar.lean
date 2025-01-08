import LC.NV.UTLC.Binders


set_option autoImplicit false


open Term_


/--
  `replace_var u v M` := The simultaneous replacement of each occurrence of the variable `u` by the variable `v` in the term `M`.
  (`u` -> `v` in `M`)
-/
def replace_var
  (u v : Symbol_) :
  Term_ → Term_
  | var_ x =>
    if u = x
    then var_ v
    else var_ x

  | app_ P Q => app_ (replace_var u v P) (replace_var u v Q)

  | abs_ x P =>
    if u = x
    then abs_ v (replace_var u v P)
    else abs_ x (replace_var u v P)


-------------------------------------------------------------------------------


theorem replace_var_id
  (M : Term_)
  (x : Symbol_) :
  replace_var x x M = M :=
  by
    induction M
    all_goals
      unfold replace_var
    case var_ x_ =>
      split_ifs
      case pos c1 =>
        rw [c1]
      case neg c1 =>
        rfl
    case app_ P_ Q_ ih_1 ih_2 =>
      rw [ih_1]
      rw [ih_2]
    case abs_ x_ P_ ih =>
      split_ifs
      case pos c1 =>
        rw [ih]
        rw [c1]
      case neg c1 =>
        rw [ih]


lemma replace_var_not_mem
  (M : Term_)
  (x y : Symbol_)
  (h1 : x ∉ M.var_set) :
  replace_var x y M = M :=
  by
    induction M
    all_goals
      unfold var_set at h1
      unfold replace_var
    case var_ x_ =>
      simp at h1

      split_ifs
      rfl
    case app_ P_ Q_ ih_1 ih_2 =>
      simp at h1
      obtain ⟨h1_left, h1_right⟩ := h1

      rw [ih_1 h1_left]
      rw [ih_2 h1_right]
    case abs_ x_ P_ ih =>
      simp at h1
      obtain ⟨h1_left, h1_right⟩ := h1

      split_ifs
      rw [ih h1_left]


theorem replace_var_not_mem_var_set
  (M : Term_)
  (x y : Symbol_)
  (h1 : ¬ x = y) :
  x ∉ (replace_var x y M).var_set :=
  by
    induction M
    case var_ x_ =>
      unfold replace_var
      split_ifs
      case pos c1 =>
        unfold var_set
        simp
        exact h1
      case neg c1 =>
        unfold var_set
        simp
        exact c1
    case app_ P_ Q_ ih_1 ih_2 =>
      unfold replace_var
      unfold var_set
      simp
      exact ⟨ih_1, ih_2⟩
    case abs_ x_ P_ ih =>
      unfold replace_var
      split_ifs
      case pos c1 =>
        unfold var_set
        simp
        exact ⟨ih, h1⟩
      case neg c1 =>
        unfold var_set
        simp
        exact ⟨ih, c1⟩


theorem replace_var_inverse
  (M : Term_)
  (x y : Symbol_)
  (h1 : y ∉ M.var_set) :
  replace_var y x (replace_var x y M) = M :=
  by
    induction M
    all_goals
      unfold var_set at h1
      simp only [replace_var]
    case var_ x_ =>
      split_ifs
      case pos c1 =>
        rw [c1]
        unfold replace_var
        simp
      case neg c1 =>
        simp at h1
        unfold replace_var
        split_ifs
        rfl
    case app_ P_ Q_ ih_1 ih_2 =>
      simp at h1
      obtain ⟨h1_left, h1_right⟩ := h1

      rw [ih_1 h1_left]
      rw [ih_2 h1_right]
    case abs_ x_ P_ ih =>
      simp at h1
      obtain ⟨h1_left, h1_right⟩ := h1

      split_ifs
      case pos c1 =>
        simp only [replace_var]
        simp
        exact ⟨c1, ih h1_left⟩
      case neg c1 =>
        simp only [replace_var]
        split_ifs
        congr
        exact ih h1_left


theorem replace_var_free_var_set_sdiff
  (M : Term_)
  (x y : Symbol_)
  (h1 : y ∉ M.var_set) :
  M.free_var_set \ {x} = (replace_var x y M).free_var_set \ {y} :=
  by
    induction M
    case var_ x_ =>
      unfold var_set at h1
      simp at h1

      unfold replace_var
      split_ifs
      case pos c1 =>
        unfold free_var_set
        rw [c1]
        simp
      case neg c1 =>
        unfold free_var_set
        simp only [Finset.sdiff_singleton_eq_erase]

        have s1 : Finset.erase {x_} x = ({x_} : Finset Symbol_) :=
        by
          apply Finset.erase_eq_of_not_mem
          simp
          exact c1
        rw [s1]

        have s2 : Finset.erase {x_} y = ({x_} : Finset Symbol_) :=
        by
          apply Finset.erase_eq_of_not_mem
          simp
          exact h1
        rw [s2]
    case app_ P_ Q_ ih_1 ih_2 =>
      unfold var_set at h1
      simp at h1
      obtain ⟨h1_left, h1_right⟩ := h1

      unfold replace_var
      unfold free_var_set
      simp only [Finset.union_sdiff_distrib]
      rw [ih_1 h1_left]
      rw [ih_2 h1_right]
    case abs_ x_ P_ ih =>
      unfold var_set at h1
      simp at h1
      obtain ⟨h1_left, _⟩ := h1

      unfold replace_var
      split_ifs
      case pos c1 =>
        rw [← c1]
        unfold free_var_set
        simp
        exact ih h1_left
      case neg c1 =>
        unfold free_var_set
        simp only [sdiff_sdiff_comm]
        congr 1
        exact ih h1_left


#lint
