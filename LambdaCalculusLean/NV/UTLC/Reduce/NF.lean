import LambdaCalculusLean.NV.UTLC.Term


mutual
def is_normal_form :
  Term_ → Prop
  | Term_.Var _ => True
  | Term_.App a n => is_neutral_normal_form a ∧ is_normal_form n
  | Term_.Abs _ n => is_normal_form n

def is_neutral_normal_form :
  Term_ → Prop
  | Term_.Var _ => True
  | Term_.App a n => is_neutral_normal_form a ∧ is_normal_form n
  | _ => False
end


mutual
def is_head_normal_form :
  Term_ → Prop
  | Term_.Var _ => True
  | Term_.App a _ => is_neutral_head_normal_form a
  | Term_.Abs _ n => is_head_normal_form n

def is_neutral_head_normal_form :
  Term_ → Prop
  | Term_.Var _ => True
  | Term_.App a _ => is_neutral_head_normal_form a
  | _ => False
end


mutual
def is_weak_normal_form :
  Term_ → Prop
  | Term_.Var _ => True
  | Term_.App a n => is_neutral_weak_normal_form a ∧ is_weak_normal_form n
  | Term_.Abs _ _ => True

def is_neutral_weak_normal_form :
  Term_ → Prop
  | Term_.Var _ => True
  | Term_.App a n => is_neutral_weak_normal_form a ∧ is_weak_normal_form n
  | _ => False
end


mutual
def is_weak_head_normal_form :
  Term_ → Prop
  | Term_.Var _ => True
  | Term_.App a _ => is_neutral_weak_head_normal_form a
  | Term_.Abs _ _ => True

def is_neutral_weak_head_normal_form :
  Term_ → Prop
  | Term_.Var _ => True
  | Term_.App a _ => is_neutral_weak_head_normal_form a
  | _ => False
end
