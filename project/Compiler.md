# Arithmetic expression compiler

The goal of this project is to implement a compiler that translates arithmetic expressions to programs for a stack machine. You have to prove that your compiler is correct.

We consider a language for arithmetic expressions:
```lean
inductive val : Type
| VBool : bool → val
| VNat : nat → val

open val

inductive bin_op : Type
| PlusOp : bin_op
| MinusOp : bin_op
| LeOp : bin_op
| LtOp : bin_op
| EqOp : bin_op

open bin_op

inductive exp : Type
| EVal : val → exp
| EOp : bin_op → exp → exp → exp
| EIf : exp → exp → exp → exp

open exp
```

---

## Exercise 1 
Define a big-step semantics for this language:
```lean
inductive big_step : exp → val → Prop
-- fill in
```

---

The first part of this project is to define the target language of your compiler: a small stack machine language with instructions in reverse Polish notation. 
The instructions are given by the following Lean definitions:
```lean
inductive instruction : Type
| IPush : val → instruction
| IOp : bin_op → instruction
| IBranch : nat → instruction
| IJump : nat → instruction
```
The intuitive semantics of these instructions is as follows:
* The instruction `IPush v` pushes a value `v` on the stack.
* The instruction `IOp op` pops two values of the stack, performs the operation `op`, and pushes the result back on the stack.
* The instruction `IBranch n` pops a Boolean from the stack, and continues execution if the Boolean is true, otherwise it skips the subsequent `n` instructions.
* The instruction `IJump n` skips `n` instructions.

---

## Exercise 2

Define a big-step semantics for the stack machine:
```lean
inductive vm_big_step : list instruction → list val → list val → Prop
-- fill in
```
You should define the semantics by processing the instructions in sequence. 
The first `list val` is the input stack, and the second `list val` is the output stack. 
The big-step semantics should be undefined (i.e., have no applicable rules) in case the wrong arguments for an instruction are on the stack, a stack underflow occurs, or an out-of-bounds jump occurs.
To define the semantics of branches and jumps, you will need to define a helper function or helper inductive predicate on lists.

---

---

## Exercise 3

Prove the following positive and negative tests of the big-step semantics:
```lean
lemma example1 : 
 vm_big_step
  [IPush (VNat 10), IPush (VNat 20), IOp EqOp, IBranch 1, IPush (VNat 1), IPush (VNat 2), IPush (VNat 3)]
  []
  [VNat 3, VNat 2]
:= sorry

lemma example2 : ¬ exists out,
 vm_big_step
  [ IPush ( VNat 10), IPush ( VBool false ), IOp EqOp ] 
  [] 
  out 
:= sorry
```
Write an additional positive test and negative test and prove these.

---

The next part of this project is to define a compiler from the arithmetic expression language to the stack machine. 
We will prove *soundness* of the compiler, which says that whenever a program has a certain outcome according to the big-step semantics for arithmetic expressions, the target program has the same outcome according to the big-step semantics for the stack machine.

---

## Exercise 4 

Implement a compiler:
```lean
def compile : exp → list instruction
-- fill in
```

---

## Exercise 5 

Prove soundness of your compiler:
```lean
lemma compile_sound (e : exp) (v : val) : big_step e v → vm_big_step (compile e) [] [v] := sorry
```
In order to prove this lemma, you might need to state and prove a more general helper lemma first.
Also, you might need to prove some helper lemmas for the function on lists that you have used for defining the big-step semantics of branches and jumps.

---

## Exercise 6

Prove completeness of the compiler (the reverse implication of soundness):
```lean
lemma compile_complete (e : exp) (v : val) : vm_big_step (compile e) [] [v] → big_step e v := sorry
```
You might need to state a more general helper lemma.

