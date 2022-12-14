import tactic -- hide
open function nat -- hide

/-
## More on `apply`

In the following example, `h` can be seen as a map
$$h : \mathbb{N} \rightarrow \\{\text{proofs}\\}$$
which gives,
for each natural number $x$, a proof of the fact that this particular $x$ satisfies $0 \leq x^2$.

This is why `apply` will work in the following example. *Lean* is smart enough to figure out which value of $x$
needs to be plugged in to match the conclusion of `h` with the goal.
-/
/- Symbol: 
≤ : \leq
-/
/- Lemma : no-side-bar
If for all x we know $0 ≤ x^2$, then $0 ≤ 3^2$.
-/
lemma l6 (h : ∀ x, 0 ≤ x^2) : 0 ≤ 3^2:=
begin
  apply h,

  
end