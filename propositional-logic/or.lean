variables A B C : Prop
#check A

section or_intro
variable a : A
include a

#check @or.intro_left A B

example : A ∨ B := or.intro_left B a

variable b : B
include b

example : A ∨ B := or.intro_right A b

/- Information "B" has to
   be given explicitly, whereas
   A can be deduced from "a"
-/
/- corresponds to

   ---a
    A
  ----- or-introduction-left
  A ∨ B


    B
  ----- or-introduction-right
  A ∨ B

-/




variable b : B
#check or.intro_right A b

example : A ∨ B := _

/- corresponds to

   ---b
    B
  ----- or-introduction-right
  A ∨ B
-/
end or_intro



section or_elim
variable h : A ∨ B
include h

variable ha : A → C
variable hb : B → C
#check (or.elim h ha hb)
#check @or.elim

example : C := or.elim h (ha) (hb) 

/- corresponds to

  ----h    ----ha   ----hb
  A ∨ B    A → C    B → C
----------------------------
            C
-/
/-
Example:
C = put nail in wall
A = hammer
B = shoe
A ∨ B = toolbox containing
one of hammer and shoe,
but you don't know which
-/
end or_elim