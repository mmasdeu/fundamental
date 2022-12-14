/-
## The `left` and `right` tactics

In the previous lemma we learned how `split` makes progress on goals involving the conjunction `∧`.
But what if the goal involves the *disjunction* `∨` (type it with `\or`)? In this case,
you first need to decide which is the side that you will try to prove. If it's the first (left)
clause, the tactic `left` will change the goal to that one, if it's the second (right) clause,
then well, you use `right`.
-/
/- Symbol:
∨ : \or
-/
/- Lemma : no-side-bar
If $a$ is $5$, then either it is $5$ or it is $7$.
-/
lemma lr0 (a : ℕ) (h : a = 5) : a = 5 ∨ a = 7 :=
begin
  left,
  assumption,




end
