import Mathlib.GroupTheory.Commutator 
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
Day 1 - Afternoon, Basics (Fundamentals)
========================================

In this session we will cover how to express two styles of proof in Lean,
These operate on the goal (the statement we are trying to prove) by changing it to a different goal,
or set of goals, hopefully in a way that makes progress towards the full proof.
The two techniques (tactics) we will cover are
- rewriting (replacing parts of the goal) - `rw` or `rewrite`
- backwards reasoning (reducing the goal to statements that imply it) - `apply`

There will be some variations on the above (and indeed other commands that do multiple rewriting or reasoning
steps for you), but these are the most fundamental.


In the real world our proofs use a mix of many different styles of reasoning all at once, but for
learning how to use it is helpful to emphasise the different nature of these types of proof.

Names
=====

Both of these fundamental tactics are low-tech, they require the user to find and say the name of the lemma
they want to use.
There are helper tactics that will suggest moves you may want to make to you (try adding a ?, e.g. `rw?`, `apply?`),
though after a while learning the naming convention of the library you are using will help you spend less
time thinking about the boring parts of your proof.

-/

/-- An example of a proof by rewriting

**Rewriting** is where we change our goal (or a part of it) to something equal in order to make progress.

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
  -- later we will learn tactics for doing these things in few or 1 step
  group
  group
  

/-
**Backwards reasoning** is where we chain implications backwards, deducing what we want to prove from a
combination of other statements (potentially even stronger ones).

A classic example of this is proving that a function defined as a combination of others has some property,
e.g. continuous, differentiable, locally constant, etc.
we do this by reasoning backwards, deconstructing the definition of the function down to its constituent pieces.
For example we might start by applying the fact that a sum of two continuous functions is continuous.

-/

open Real

example : Continuous (fun x ↦ (sin (x ^ 2)) ^ 3 + cos (5 * x)) := by
  -- apply?
  apply Continuous.add
  apply Continuous.pow
  apply Continuous.comp continuous_sin
  apply continuous_pow
  apply Continuous.comp continuous_cos
  apply Continuous.mul
  apply continuous_const
  apply continuous_id


-- TODO apply .add

/-
But this is obvious!
Any mathematician worth their salt knows that such a function is continuous just by looking at it,
its a composition of polynomials and things polynomial in `cos` and `sin`.

Mathlib has tactics for automatically doing some such reasoning chains, but don't use it for the
exercises!

-/

example : Continuous (fun x ↦ (sin (x ^ 2)) ^ 3 + cos (5 * x)) := by
  continuity?
  -- aesop (options := { terminal := true }) (rule_sets [$(Lean.mkIdent `Continuous):ident])

/-
Some differences between rewriting and applying:
- Rewriting can take place almost anywhere in the goal, but apply generally has to match the outermost thing you are trying to prove
  e.g. if you are trying to prove an and satement, you'll need to split it in to two goals before trying apply
- Sometimes many rewrites are possible using the same lemma, and specifying more of the arguments will help
-/


example :
  Continuous ((fun x ↦ if x < 0 then (1 : ℝ)  else -1) + 
               fun x ↦ if x < 0 then -1 else x + 1) := by
  apply Continuous.add <;> dsimp
  apply continuous_if
  intro a ha
  simp [frontier_eq_inter_compl_interior] at ha -- TODO
  sorry
  sorry
  sorry
  sorry