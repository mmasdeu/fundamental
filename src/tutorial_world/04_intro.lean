import tactic -- hide
open function nat -- hide

/-
## The `intro` tactic

Many statements in mathematics start with the phrase: "for all $x$ such that...". The way to proceed is usually
to suppose that we are given an $x$ with the given condition, and then prove something about it.

The tactic `intro` allows for this. It takes a parameter, which will be the name given to the variable.

It also works in statements of the form `P → Q` (we can think of it as equivalent to "To each proof of $P$ we produce a proof of $Q$").

In the following lemma, we will need to apply the `intro` tactic twice to get to business.

**Pro tip:** the `revert` tactic does exactly the opposite.
-/

/- Lemma : no-side-bar
For all $a$, if $a = 3$ then $a + 1 = 4$.
-/
lemma l4 : ∀ (a : ℕ),  a = 3 → a + 1 = 4 :=
begin
  intro a,
  intro h,
  rw h,


  
end