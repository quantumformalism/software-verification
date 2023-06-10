# Teaching repository for Software Verification

<details><summary>Motivation</summary>

How can we ensure that software does not crash and is guaranteed to be correct? In this course we tackle this question by viewing programs and programming languages as mathematical objects. In this way we can use logic to prove properties about programs and thereby guarantee that software is correct. To make reasoning about actual programs and programming languages feasible, we will not be doing these proofs by hand, but instead use a tool called a proof assistant. Such tools help building proofs that can be checked by a computer. As we will show during this course, proof assistants turn the activity of doing proofs into programming.
</details>
  
## Contact & Help

Join our chat at https://quantumformalism.zulipchat.com/.

## Overview of the course


<details><summary>Introduction</summary>

  * Presentation of the learning material
  * Explanation of learning mode: flipped classroom
  * Means of contact (git repository, Zulip chat)
  * Introduction to Lean
  
</details>

<details><summary>Propositional logic</summary>

  * Logic of statements https://en.wikipedia.org/wiki/Propositional_calculus
  * Study of logical operations "and", "or", and implication
  * Proofs of propositions in natural deduction style https://en.wikipedia.org/wiki/Natural_deduction
  
</details>

<details><summary>Predicate logic aka first order logic</summary>

  * Study of quantifiers, universal ("for all") and existential ("there exists")
  * https://en.wikipedia.org/wiki/First-order_logic
  
</details>

<details><summary>Functional programming and verification</summary>

  * Programming style supported in Haskell, Ocaml, Python, etc, https://en.wikipedia.org/wiki/Functional_programming
  * Functional programs are particularly well-suited for formal verification
  * Lean supports functional programming natively
  
</details>


<details><summary>Use of a computer proof assistant</summary>
  
  * Computer proof assistants provide a language suitable for both programming and proving: an algorithm can be both implemented and proved correct in the same language.
  * Computer proof assistants check the correctness of user-provided proofs.
  * Programs can be executed directly in the computer proof assistant.

</details>



  

## <a name="meetings">Meetings

TBA

## Plan

For every week, a workplan for you is specified on the dedicated page:
  
- [Week 1](./Week1.md)
- [Week 2](./Week2.md)
- [Week 3](./Week3.md)
- [Week 4](./Week4.md)
- [Week 5](./Week5.md)
- [Week 6](./Week6.md)

The workplans will be provided on a rolling basis.
  
  
## External resources
  
### Materials used in the course
  
  - Book [Logic and Proof](https://leanprover.github.io/logic_and_proof/)
  - Course [Logical Verification](https://lean-forward.github.io/logical-verification/2021/index.html)
    - [Textbook](https://github.com/benediktahrens/logical_verification_2021/raw/main/hitchhikers_guide.pdf)
    - [Git repository with Lean files](https://github.com/benediktahrens/logical_verification_2021)
    - Lecture videos are available on [Logical Verification](https://lean-forward.github.io/logical-verification/2021/index.html)
  
### Additional resources
  - [Lean in the browser](https://leanprover-community.github.io/lean-web-editor/)
  - [Installation instructions for Lean](https://github.com/benediktahrens/logical_verification_2021/blob/main/README.md)
  - [Lean tutorial](https://leanprover.github.io/theorem_proving_in_lean/)
  - Book [Concrete Semantics](http://concrete-semantics.org/), using [Isabelle/HOL](https://en.wikipedia.org/wiki/Isabelle_(proof_assistant))
  - Our [Zulip server](https://quantumformalism.zulipchat.com)
