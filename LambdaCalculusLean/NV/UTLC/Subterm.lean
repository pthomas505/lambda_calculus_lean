import LambdaCalculusLean.NV.UTLC.Term


set_option linter.style.docString false
set_option linter.style.emptyLine false


/--
  `Term_.subterm_list M` := The list of all of the subterms of a term `M`.
  Definition 1.3.5
-/
def Term_.subterm_list : Term_ → List Term_
  | Var x => [Var x]
  | App M N => M.subterm_list ++ N.subterm_list ++ [App M N]
  | Abs x M => M.subterm_list ++ [Abs x M]

#eval List.map Term_.toString (Term_| (x z)).subterm_list
#eval List.map Term_.toString (Term_| (λ x. (x x))).subterm_list
#eval List.map Term_.toString (Term_| ((λ x. (x x)) (λ x. (x x)))).subterm_list


-- reflexivity
theorem lemma_1_3_6_refl
  (M : Term_) :
  M ∈ M.subterm_list :=
  by
    cases M
    case Var v =>
      unfold Term_.subterm_list
      rewrite [List.mem_singleton]
      apply Eq.refl
    case App P Q =>
      unfold Term_.subterm_list
      exact List.mem_concat_self
    case Abs v P =>
      unfold Term_.subterm_list
      exact List.mem_concat_self


-- transitivity
theorem lemma_1_3_6_trans
  (L M N : Term_)
  (h1 : L ∈ M.subterm_list)
  (h2 : M ∈ N.subterm_list) :
  L ∈ N.subterm_list :=
  by
    induction N
    case Var v =>
      unfold Term_.subterm_list at h2
      rewrite [List.mem_singleton] at h2
      rewrite [h2] at h1
      exact h1
    case App P Q ih_1 ih_2 =>
      unfold Term_.subterm_list at h2
      simp only [List.append_assoc, List.mem_append, List.mem_cons, List.not_mem_nil] at h2

      cases h2
      case inl h2 =>
        unfold Term_.subterm_list
        simp only [List.append_assoc, List.mem_append, List.mem_cons, List.not_mem_nil]
        left
        exact ih_1 h2
      case inr h2 =>
        cases h2
        case inl h2 =>
          unfold Term_.subterm_list
          simp only [List.append_assoc, List.mem_append, List.mem_cons, List.not_mem_nil]
          right
          left
          exact ih_2 h2
        case inr h2 =>
          cases h2
          case inl h2 =>
            rewrite [h2] at h1
            exact h1
          case inr h2 =>
            contradiction
    case Abs v P ih =>
      unfold Term_.subterm_list at h2
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil] at h2

      cases h2
      case inl h2 =>
        unfold Term_.subterm_list
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil]
        left
        exact ih h2
      case inr h2 =>
        cases h2
        case inl h2 =>
          rewrite [h2] at h1
          exact h1
        case inr h2 =>
          contradiction


/--
  `is_proper_subterm L M` := True if and only if `L` is a proper subterm of `M`.
  Definition 1.3.8
-/
def is_proper_subterm
  (L M : Term_) :
  Prop :=
  L ∈ M.subterm_list ∧ ¬ L = M

instance
  (L M : Term_) :
  Decidable (is_proper_subterm L M) :=
  by
    unfold is_proper_subterm
    infer_instance
