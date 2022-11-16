import tactic -- hide
open function nat -- hide

/-
## Some more on `rw`

We can do replacements in hypotheses, not just on the goal, by using `at`. For instance, in the example below
we can substitute the value of $a=3$ in `h1` (via `rw h2 at h1`), or substituting the value of $a=b+c$
in `h2` (via `rw h1 at h2`). This will allow you to close the goal without using `assumption`, by
doing one more `rw`.
-/

/- Lemma : no-side-bar
If $a = b+c$ and $a = 3$, then $b + c = 3$.
-/
lemma l3 (a b c : ℕ) (h1 : a = b + c) (h2 : a = 3) : b + c = 3:=
begin
  rw h2 at h1,
  rw ←h1,
end