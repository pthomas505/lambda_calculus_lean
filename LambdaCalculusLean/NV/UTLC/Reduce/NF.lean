import LC.NV.UTLC.Term


set_option autoImplicit false


open Term_


mutual
def is_normal_form :
  Term_ → Prop
  | var_ _ => True
  | app_ a n => is_neutral_normal_form a ∧ is_normal_form n
  | abs_ _ n => is_normal_form n

def is_neutral_normal_form :
  Term_ → Prop
  | var_ _ => True
  | app_ a n => is_neutral_normal_form a ∧ is_normal_form n
  | _ => False
end


mutual
def is_head_normal_form :
  Term_ → Prop
  | var_ _ => True
  | app_ a _ => is_neutral_head_normal_form a
  | abs_ _ n => is_head_normal_form n

def is_neutral_head_normal_form :
  Term_ → Prop
  | var_ _ => True
  | app_ a _ => is_neutral_head_normal_form a
  | _ => False
end


mutual
def is_weak_normal_form :
  Term_ → Prop
  | var_ _ => True
  | app_ a n => is_neutral_weak_normal_form a ∧ is_weak_normal_form n
  | abs_ _ _ => True

def is_neutral_weak_normal_form :
  Term_ → Prop
  | var_ _ => True
  | app_ a n => is_neutral_weak_normal_form a ∧ is_weak_normal_form n
  | _ => False
end


mutual
def is_weak_head_normal_form :
  Term_ → Prop
  | var_ _ => True
  | app_ a _ => is_neutral_weak_head_normal_form a
  | abs_ _ _ => True

def is_neutral_weak_head_normal_form :
  Term_ → Prop
  | var_ _ => True
  | app_ a _ => is_neutral_weak_head_normal_form a
  | _ => False
end
