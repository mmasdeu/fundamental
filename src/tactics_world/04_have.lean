import tactic -- hide
import data.real.basic -- hide

/-
## The `have` tactic

It is common in proofs to introduce auxiliary results, or claims, that help towards the goal. *Lean*
allows for this kind of structure, by allowing you to insert new hypotheses (as long as you prove them,
of course). This is done with the `have` tactic. The syntax is `have h : P,` where `h` is the name
you want to give to the new hypothesis (check that it doesn't exist already or you will run intro problems)
and `P` is a predicate like `x + 3 = 5`. You will get two goals, the first one will be to prove `P`,
and the second one will be the original goal. In the second one, you will have `h` available.

The next lemma cannot be proven by `ring` directly, since it involves an arbitrary exponent. There
are tactics that work with these kind of equations, but we will do something easier. If we can prove
first that $x+y=y+x$, then replacing that equality on the left-hand side will immediately finish the
goal. So start with `have h : x + y = y + x,` and work from there.
-/

/- Lemma : no-side-bar
For all $n$, we have $(x+y)^n=(y+x)^n$.
-/
lemma h0 (x y : ℝ) (n : ℕ) : (x + y)^n = (y + x)^n :=
begin
  have h : x + y = y + x,
  {
    ring,
  },
  rw h,



end
