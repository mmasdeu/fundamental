import tactic -- hide
open function nat -- hide

/-
## More on `rw`

We have seen that the `rw` tactic replaces occurrences of $a$ with $b$ if we have `h : a = b`.
If we want to replace the occurrences of $b$ into $a$, we can use the fact that `h.symm` is a proof of
$b = a$ (and hence do `rw h.symm`) or use `rw ← h` (type `←` with \l). Try it below.
-/

/-
**Pro tip:** In very rare occasions, we might end up with a goal of the form `a = a`, where
`a` is a very complicated expression. This can be closed with the `refl` tactic (it means
*reflexivity*).
-/

/- Symbol:
← : \l
-/
/- Lemma : no-side-bar
If $a = b + c$ and $a = 3$, then $b + c = 3$.
-/
lemma l2 (a b c : ℕ) (h1 : a = b + c) (h2 : a = 3): b + c = 3:=
begin
  rw ← h1,
  assumption,

  
end
