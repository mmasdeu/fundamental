import tactic -- hide
import data.real.basic -- hide

/-
## The `cases` tactic

We have talked before about how to deal with a conjunction `∧` in the goal. Sometimes,
we may have a conjuntion in a hypothesis. In this case, the tactic `cases` breaks it into
two new hypotheses. If we do `cases h with h1 h2` it will replace a hypothesis of
the form `h : P ∧ Q` into `h1 : P` and `h2 : Q`.

In the following lemma, a direct application of `assumption` won't work,
because the goal is not *exactly* our assumption. We need to break `h` into two.

**Pro tip:** If there is a double implication in `h`, then again we can use `cases h`
to break it into two.

**Pro tip 2:** We can refer to the two parts of `h` as `h.1` and `h.2`, so sometimes
we won't need to break `h`...

-/

/- Lemma : no-side-bar
If $a=5$ and $b=3$, then $a=5$.
-/
lemma c1 (a b : ℕ) (h : a = 5 ∧ b = 3) : a = 5 :=
begin
  cases h,
  assumption,


end