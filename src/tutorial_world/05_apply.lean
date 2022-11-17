import tactic -- hide
open function nat -- hide

/-
## The `apply` tactic

If we have a proof of the implication `h : P → Q` and we want to prove `Q`, then it is enough to prove `P`
instead. In mathematics, we may say: "To prove `Q` it suffices to prove `P`, since by `h` we know that
it implies `Q`". We then forget about `Q` and prove `P` instead.

In *Lean*, this reasoning is realised by the `apply` tactic. If the goal is `Q` and we do `apply h,`,
the goal gets changed to `P` instead. Note that it may well be that `P` is impossible to prove,
so we might be able to backtrack if we `apply` the wrong statements...
-/

/- Lemma : no-side-bar
If $P$ implies $Q$ and we know $P$, then we can prove $Q$.
-/
lemma l5 (P Q : Prop) (h : P → Q) (hp : P) : Q :=
begin
  apply h,
  assumption,
end