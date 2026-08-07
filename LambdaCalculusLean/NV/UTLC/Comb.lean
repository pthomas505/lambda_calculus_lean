import LambdaCalculusLean.NV.UTLC.Term


def I_ : Term_ := (Term_| (λ x. x))
def K_ : Term_ := (Term_| (λ x. (λ y. x)))
def omega_ : Term_ := (Term_| (λ x. (x y)))
def Omega_ : Term_ := (Term_| (omega_ omega_))


def true_ : Term_ := (Term_| (λ x. (λ y. x)))
def false_ : Term_ := (Term_| (λ x. (λ y. y)))

def not_ : Term_ := (Term_| (λ b . ((b false_) true_)))
