# SAT Solver

The goal of this project is to implement a Boolean Satisfiability (SAT) solver in Lean and to prove soundness of your implementation.

Boolean formulas are given by the following grammar:
```
 p, q ::= x | ⊤ | ⊥ | p ∧ q | p ∨ q | p → q | ¬p
```
Here, `x` ranges over an infinite set of propositional variables. 
Examples of formulas are `(x ∨ ¬y) ∧ (¬x ∨ y)`, and `¬y → (x ∨ y)`, and `x ∧ ¬x ∧ ⊤`.

A Boolean formula `p` is said to be satisfiable in case its truth table contains at least one row whose outcome is 1.
For example, the formula `¬ y → (x ∨ y)` has the truth table
```
x | y | (¬ y → (x ∨ y))
f | f | f
t | f | t
f | t | t
t | t | t
```
and thus is satisfiable.
The formula `x ∧ ¬ x ∧ ⊤` has the truth table
```
x | (x ∧ ¬ x ∧ ⊤)
f | f
t | f
```
and hence is not satisfiable.


The first part of this project is to represent Boolean formulas in Lean and to formally define the notion of satisfiability.

---

## Exercise 1

```lean
inductive form : Type
| FVar : string → form
--fill in
```

---

## Exercise 2


Give Lean definitions of type `form` corresponding to 
- `(x ∨ ¬y) ∧ (¬x ∨ y)`
- `¬y → (x ∨ y)`
- `x ∧ ¬x ∧ ⊤`

---

In order to define satisfiability we introduce the notion of a valuation, which is a function that assigns true or false to each propositional variable.

```lean
def valuation : Type := string → bool
```


---

## Exercise 3

Define *validity* of Boolean formulas (using the 'truth table semantics') by filling out the following definition:

```lean
def valid : valuation → form → Prop := sorry
--fill in
```

---


A formula is said to be satisfiable if there exists a valuation that makes the formula true. This corresponds to the following definition in Lean:

```lean
def satisfiable (p : form) : Prop := ∃ V : valuation, valid V p
```

---

## Exercise 4

Prove in Lean that `(x ∨ ¬y) ∧ (¬x ∨ y)` and `¬y → (x ∨ y)` are satisfiable. You should create two lemmas of the shape below, replacing `foo` by the respective formulas in the lemma:

```lean
definition foo : form := sorry
lemma testX : satisfiable foo := sorry
```

---

## Exercise 5

Define a function `find_valuation` that given a formula `p` computes a valuation in which `p` is true. 
You should implement this function by enumerating all possible valuations, i.e., you should generate the formula's truth table and check if there is a row whose outcome is 1. 
The function `find_valuation` should yield `none` in case no such valuation exists.

```lean
def find_valuation (p : form) : option valuation := sorry
```

---

We now define our SAT solver as follows:

```lean
def solver (p : form) : bool :=
match find_valuation p with
| option.some _ := tt
| option.none   := ff
end
```

---

## Exercise 6

Explain the difference between `satisfiable` and `solver`.

---

## Exercise 7

Write 2 positive and 2 negative tests of the solver and prove these through proof by simplication via the `refl` tactic.

----

## Exercise 8

Prove that `solver` is sound. That means:

```lean
theorem solver_sound (p : form) : solver p = tt → satisfiable p := sorry
```

You might want to state a helper lemma first, which you should prove by varying the induction hypothesis.

---

## Exercise 9

Write an optimizer that simplifies a Boolean formula using the laws below, and prove correctness of your optimizer.

- `x ∧ ⊤ = x`
- `⊤ ∧ x = x`
- `x ∧ ⊥ = ⊥`
- `⊥ ∧ x = ⊥`
- `x ∨ ⊤ = ⊤`
- `⊤ ∨ x = ⊤`
- `x ∨ ⊥ = x`
- `⊥ ∨ x = x`

