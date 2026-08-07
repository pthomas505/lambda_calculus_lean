import LambdaCalculusLean.NV.UTLC.Term


set_option linter.style.docString false
set_option linter.style.longLine false
set_option linter.style.emptyLine false


/--
  `replace_var x y M` := The simultaneous replacement of each occurrence of the variable `x` in the term `M` by the variable `y`.
-/
def replace_var
  (x y : String) :
  Term_ → Term_
  | Term_.Var v =>
    if x = v
    then Term_.Var y
    else Term_.Var v

  | Term_.App P Q =>
    Term_.App (replace_var x y P) (replace_var x y Q)

  | Term_.Abs v P =>
    if x = v
    then Term_.Abs y (replace_var x y P)
    else Term_.Abs v (replace_var x y P)
