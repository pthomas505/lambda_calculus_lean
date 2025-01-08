import LC.NV.UTLC.Term


set_option autoImplicit false


open Term_


def I_ : Term_ := abs_ "x" (var_ "x")
def K_ : Term_ := abs_ "x" (abs_ "y" (var_ "x"))
def omega_ : Term_ := abs_ "x" (app_ (var_ "x") (var_ "x"))
def Omega_ : Term_ := app_ omega_ omega_


def true_ : Term_ := abs_ "x" (abs_ "y" (var_ "x"))
def false_ : Term_ := abs_ "x" (abs_ "y" (var_ "y"))

def not_ : Term_ := abs_ "b" (app_ (app_ (var_ "b") false_) true_)
