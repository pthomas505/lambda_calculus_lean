import LC.NV.UTLC.Binders


set_option autoImplicit false


open Term_


/--
  `replace_free v N M` := The simultaneous replacement of each occurrence of the variable `v` by the term `N` in the term `M`.
  `M [ v := N ]`
  (`v` -> `N` in `M`)
-/
def replace_free
  (v : Symbol_)
  (N : Term_) :
  Term_ → Term_
  | var_ x =>
    if v = x
    then N
    else var_ x

  | app_ P Q => app_ (replace_free v N P) (replace_free v N Q)

  | abs_ x P =>
    if v = x
    then abs_ x P
    else abs_ x (replace_free v N P)


-------------------------------------------------------------------------------


-- [1] lemma_1_2_5_iii_b
lemma replace_free_id
  (M : Term_)
  (x : Symbol_) :
  replace_free x (var_ x) M = M :=
  by
    induction M
    all_goals
      unfold replace_free
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
        rfl
      case neg c1 =>
        rw [ih]


-- [1] lemma_1_2_5_i_b
lemma replace_free_not_mem
  (M : Term_)
  (x : Symbol_)
  (N : Term_)
  (h1 : x ∉ M.free_var_set) :
  replace_free x N M = M :=
  by
    induction M
    all_goals
      unfold free_var_set at h1
      unfold replace_free
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

      split_ifs
      case pos c1 =>
        rfl
      case neg c1 =>
        have s1 : x ∉ P_.free_var_set := by tauto
        specialize ih s1
        rw [ih]


lemma replace_free_mem_free_var_set
  (M : Term_)
  (x : Symbol_)
  (N : Term_)
  (y : Symbol_)
  (h1 : y ∈ M.free_var_set)
  (h2 : ¬ x = y) :
  y ∈ (replace_free x N M).free_var_set :=
  by
    induction M
    case var_ x_ =>
      unfold free_var_set at h1
      simp at h1
      rw [h1] at h2

      unfold replace_free
      split_ifs
      unfold free_var_set
      simp
      exact h1
    case app_ P_ Q_ ih_1 ih_2 =>
      unfold free_var_set at h1
      simp at h1

      simp only [free_var_set]
      simp
      tauto
    case abs_ x_ P_ ih =>
      unfold replace_free
      split_ifs
      case pos c1 =>
        exact h1
      case neg c1 =>
        unfold free_var_set at h1
        simp at h1
        unfold free_var_set
        simp
        tauto


lemma replace_free_not_mem_free_var_set
  (M : Term_)
  (x : Symbol_)
  (N : Term_)
  (h1 : x ∉ N.free_var_set) :
  x ∉ (replace_free x N M).free_var_set :=
  by
    induction M
    case var_ x_ =>
      unfold replace_free
      split_ifs
      case pos c1 =>
        exact h1
      case neg c1 =>
        unfold free_var_set
        simp
        exact c1
    case app_ P_ Q_ ih_1 ih_2 =>
      unfold replace_free
      unfold free_var_set
      simp
      exact ⟨ih_1, ih_2⟩
    case abs_ x_ P_ ih =>
      unfold replace_free
      split_ifs
      case pos c1 =>
        unfold free_var_set
        simp
        intro contra
        exact c1
      case neg c1 =>
        unfold free_var_set
        simp
        intro a1
        contradiction


lemma replace_free_not_mem_either_free_var_set
  (M : Term_)
  (x : Symbol_)
  (N : Term_)
  (y : Symbol_)
  (h1 : y ∉ M.free_var_set)
  (h2 : y ∉ N.free_var_set) :
  y ∉ (replace_free x N M).free_var_set :=
  by
    induction M
    all_goals
      unfold free_var_set at h1
    case var_ x_ =>
      simp at h1

      unfold replace_free
      split_ifs
      case pos c1 =>
        exact h2
      case neg c1 =>
        unfold free_var_set
        simp
        exact h1
    case app_ P_ Q_ ih_1 ih_2 =>
      simp at h1

      unfold replace_free
      unfold free_var_set
      simp
      tauto
    case abs_ x_ P_ ih =>
      simp at h1

      unfold replace_free
      split_ifs
      case pos c1 =>
        unfold free_var_set
        simp
        exact h1
      case neg c1 =>
        unfold free_var_set
        simp
        intro a1
        apply h1
        by_contra contra
        apply ih; exact contra; exact a1


lemma replace_free_inverse
  (M : Term_)
  (x y : Symbol_)
  (h1 : y ∉ M.var_set) :
  replace_free y (var_ x) (replace_free x (var_ y) M) = M :=
  by
    induction M
    all_goals
      unfold var_set at h1
      simp only [replace_free]
    case var_ x_ =>
      simp at h1

      split_ifs
      case pos c1 =>
        rw [c1]
        unfold replace_free
        simp
      case neg c1 =>
        unfold replace_free
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
      specialize ih h1_left

      split_ifs
      case pos c1 =>
        unfold replace_free
        split_ifs
        congr
        have s1 : y ∉ P_.free_var_set :=
        by
          exact not_mem_var_set_imp_not_mem_free_var_set y P_ h1_left
        exact replace_free_not_mem P_ y (var_ x) s1
      case neg c1 =>
        unfold replace_free
        split_ifs
        rw [ih]


#lint
