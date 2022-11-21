import tactic -- hide
import data.real.basic -- hide

/-
## Divisibility

In the quest for proving an interesting result about Fibonacci numbers
it will be useful to have the following lemma, that allows to deduce
the divibility of a sum from the divisibility of the summands.

Recall that a natural number $d$ divides another one $n$ if there is some $t$
such that $n = dt$. Below you have the *Lean* definition:
-/
lemma divides_def {d n : ℕ} : d ∣ n ↔ ∃ t, n = d * t
:= iff.rfl -- hide

/- Axiom : divides_def
d ∣ n ↔ ∃ t, n = d * t
-/



/- Lemma :
If $k$ divides $n$ and $m$, then $k$ divides $m + n$.
-/
lemma divides_add {k n m : ℕ} (hn : k ∣ n) (hm : k ∣ m) : k ∣ m + n :=
begin
  cases hn with n1 hn1,
  cases hm with m1 hm1,
  use n1 + m1,
  rw hn1,
  rw hm1,
  ring,



  
end

