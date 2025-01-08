import Lean

set_option autoImplicit false


-- https://www.andres-loeh.de/LambdaPi/


open Lean Elab Meta


inductive Name_ : Type
| Global : String → Name_
| Local : Int → Name_
| Quote : Int → Name_
deriving Inhabited, DecidableEq, Repr


inductive Type_ : Type
-- base type
| TFree : Name_ → Type_
-- function type
| Fun : Type_ → Type_ → Type_
deriving Inhabited, DecidableEq, Repr


mutual
-- inferable terms
inductive ITerm_ : Type
-- annotated term
| Ann : CTerm_ → Type_ → ITerm_
-- bound variable
| Bound : Nat → ITerm_
-- free variable
| Free : Name_ → ITerm_
-- application
| App : ITerm_ → CTerm_ → ITerm_
deriving Inhabited, DecidableEq, Repr


-- checkable terms
inductive CTerm_ : Type
-- inferable term
| Inf : ITerm_ → CTerm_
-- lambda abstraction
| Lam : CTerm_ → CTerm_
deriving Inhabited, DecidableEq, Repr
end


-- A value is either a neutral term, i.e., a variable applied to a (possibly empty) sequence of values, or it is a lambda abstraction.

mutual
inductive Value_ : Type
-- lambda abstraction
| VLam : Value_ → Value_ → Value_
-- neutral term
| VNeutral : Neutral_ → Value_
deriving DecidableEq, Repr


inductive Neutral_ : Type
-- variable
| NFree : Name_ → Neutral_
-- application
| NApp : Neutral_ → Value_ → Neutral_
deriving Inhabited, DecidableEq, Repr
end


def vfree
  (n : Name_) :
  Value_ :=
  Value_.VNeutral (Neutral_.NFree n)


def Env_ : Type := List Value_

def NameEnv_ (v) := AssocList Name_ v

/-
  iEval :: ITerm -> (NameEnv Value,Env) -> Value
  iEval (Ann  e _)    d  =  cEval e d
  iEval (Free  x)     d  =  case lookup x (fst d) of Nothing ->  (vfree x); Just v -> v
  iEval (Bound  ii)   d  =  (snd d) !! ii
  iEval (e1 :@: e2)   d  =  vapp (iEval e1 d) (cEval e2 d)

  vapp :: Value -> Value -> Value
  vapp (VLam f)      v  =  f v
  vapp (VNeutral n)  v  =  VNeutral (NApp n v)

  cEval :: CTerm -> (NameEnv Value,Env) -> Value
  cEval (Inf  ii)   d  =  iEval ii d
  cEval (Lam  e)    d  =  VLam (\ x -> cEval e (((\(e, d) -> (e,  (x : d))) d)))
-/
