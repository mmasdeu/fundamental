import tactic -- hide
import data.real.basic -- hide

/-
## The `rw show` trick

This is more a trick than a tactic, but it's extremely useful. In the previous level
we wanted to change $x+y$ into $y+x$ so we introduced a new hypothesis which we immediately
`rw`rote. It seems a waste of effort, and we can shorten the proof using the `rw show A = B, by {...}`
trick. Inside the `{...}` block you will have to prove the equality $A = B$, and then this will be
rewritten in the goal. If you only need one tactic to prove $A=B$, you can remove the braces altogether.

Try to prove this lemma with only one line starting with `rw show`.
-/

/- Lemma : no-side-bar
For all $n$, we have $(x+y)^n=(y+x)^n$.
-/
lemma h0' (x y : ℝ) (n : ℕ) : (x + y)^n = (y + x)^n :=
begin
  rw show x + y = y + x, by ring,



end