import tactic -- hide
open function nat -- hide

/-
## Some more on `apply`

In the following example, `h` eats a number $x$ and a proof of the fact that $1\leq x$, and gives
a proof of the fact that $1\leq x^2$. So if we `apply h`, *Lean* can figure out that $x$ must be set to
$2$ (we could just as well type `apply h 2` to help him), but then it will want a proof of the fact that $1\leq 2$. In this case, *Lean* has in its library
a proof of
this fact, called `one_le_two`, which we can `apply` after `h`.
-/

/- Lemma : no-side-bar
Knowing that for all x, if $1\leq x$ then $1 ≤ x^2$, we can prove that $1 ≤ 2^2$.
-/
lemma l7 (h : ∀ x, 1 ≤ x → 1 ≤ x^2) : 1 ≤ 2^2:=
begin
  apply h,
  apply one_le_two,
end