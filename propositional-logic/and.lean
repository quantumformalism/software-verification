variables A B : Prop
#check A
#check B

section and_intro
--Reminder:
--variables are assumptions
variable a : A
variable b : B
include a b
#check a
#check and.intro a b
--Synonymous with
#check (⟨ a , b ⟩ : A ∧ B)
--written \ langle , \ rangle
--this needs type annotation


example : A ∧ B := and.intro a b

/- corresponds to

 a--- ---b
   A   B
   ----- and-introduction
   A ∧ B
-/
end and_intro


section and_elim
variable h : A ∧ B
include h
#check h
#check and.left h
#check h.left --synonymous
#check and.right h

example : A := h.left

example : B := h.right

/- correspond to

  ------ h
   A ∧ B
   ----- and-elimination-left
     A

and

   ----- h
   A ∧ B
   ----- and-elimination-right
     B
-/
end and_elim
