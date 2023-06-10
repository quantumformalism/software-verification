variables A B : Prop
#check A

section impl_intro

variable a : A
include a

example : B := _

end impl_intro

section impl_intro_2
example : A → B := 
  assume a : A, _
end impl_intro_2

/-
"assume a : A" is
implication-introduction


   ---a
    A
    .
    .
    .
    B
--------- assume a
  A → B

-/



section impl_elim
variable f : A → B
variable a : A
include f a
#check f a

example : B := f a


/- corresponds to

 f-----   ---a
  A → B    A
  ---------- implication-elim
       B
-/
end impl_elim

