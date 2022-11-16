import tactic -- hide
open function nat -- hide

/-
## The `rw` tactic

The next tactic to learn is the `rw` tactic (short for `rewrite`). If we have a proof $h$ of an equality
$a=b$, then `rw h` will replace all occurrences of $a$ in the goal with $b$. It also works with `↔` instead of `=`.
That is, if we have two equivalent statements, it will replace one with the other.

In the example at hand, we have a proof $h$ of the fact that $a=3$. We want to prove that $a+5=8$,
which we could do by substituting in the value of $a$. Try to erase the `sorry` and replace it with
`rw h,` and see if it works.
-/

/- Lemma : no-side-bar
If $a = 3$, then $a + 5 = 8$.
-/
lemma l1 (a : ℕ) (h : a = 3) : a + 5 = 8 :=
begin
  rw h,
end
