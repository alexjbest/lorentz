import Mathlib.GroupTheory.Commutator 

/-!
Day 1 - Afternoon, Basics (Fundamentals)
========================================

In this session we will cover how to express two styles of proof in a proof assistant
- rewriting
- backwards reasoning

There will be some variations on the above (other commands that do multiple rewriting or reasoning
steps for you).

**Rewriting** is where we change our goal (or a part of it) to something equal in order to make progress.
**Backwards reasoning** is where we chain implications backwards, deducing what we want to prove from a
combination of other statements (potentially even stronger ones).

In the real world our proofs use a mix of many different styles of reasoning all at once, but for
learning how to use it is helpful to emphasise the different nature of these types of proof.

-/

/-- An example of a proof by rewriting

Here the commutator of two elements of a group

-/


example {G : Type} [Group G] (g h : G) : ⁅g, h⁆⁻¹ = ⁅h, g⁆ := by
  rw [commutatorElement_def]
  rw [commutatorElement_def]
  rw [mul_inv_rev]
  rw [mul_inv_rev]
  rw [mul_inv_rev]
  rw [inv_inv]
  rw [inv_inv]
  rw [mul_assoc]
  rw [mul_assoc]


example : Continuous  id := sorry