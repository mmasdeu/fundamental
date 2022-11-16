import tactic -- hide
import data.real.basic -- hide

/-
## Some more on `cases`

There is another application of the swiss-army knife `cases`. If we have `h : ∃ x, P x`, then sometimes we want to have
a witness for such an $x$. There are possibly many choices for such an $x$, but we
will just get one. When one does `cases h with x hx`, there will be a new value `x`
added to the list of "hypotheses", and the fact `hx : P x` for us to use.
-/

/- Lemma : no-side-bar
If we have $\sqrt{2}$ then we also have $\sqrt{8}$.
-/
lemma c3 (h : ∃ (x : ℝ), x^2 = 2) : ∃ (x : ℝ), x^2 = 8 :=
begin
cases h with r hr,
use 2 * r,
rw show (2 * r) ^ 2 = 2^2 * r^2, by ring,
rw hr,
ring,

  


end