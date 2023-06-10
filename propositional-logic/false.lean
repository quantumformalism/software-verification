section false_elim

#check false
variable f : false
include f

#check false.elim
#check false.elim f
--prints false.elim f : ?M_1

--signals that one can prove
--anything from false


variable A : Prop
#check A
example : A := false.elim f

/- corresponds to

  false
  ----- false-elim
    A
-/

end false_elim