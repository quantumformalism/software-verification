
-- proof using lambda terms directly
example (A : Prop) : A → A ∧ A :=
  assume (a : A), and.intro a a
  
-- proof using tactics
example (A : Prop) : A → A ∧ A :=
begin
  intro a,
  apply and.intro,
  { apply a },
  { apply a }
end

-- proof using lambda terms directly
example (A B : Prop) : A ∧ (A → B) → B :=
  assume h : A ∧ (A → B),
  h.2 h.1

-- proof using tactics
example (A B : Prop) : A ∧ (A → B) → B :=
begin
  intro h,
  apply h.2,
  apply h.1
end

-- proof using lambda terms directly
example (A B C : Prop) : (A → (B → C)) → (A ∧ B → C) :=
  assume (h : A → (B → C)),
  assume (j : A ∧ B),
  h (j.1) (j.2)

-- proof using tactics
example (A B C : Prop) : (A → (B → C)) → (A ∧ B → C) :=
begin
  intro h,
  intro j,
  apply h,
   { apply j.1 } ,
   { apply j.2 } 
end

