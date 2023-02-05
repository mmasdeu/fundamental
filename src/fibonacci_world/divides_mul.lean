import tactic -- hide
import data.real.basic -- hide

/-
## Divisibility of an obvious multiple

Recall that a natural number $d$ divides another one $n$ if there is some $t$
such that $n = dt$. Below you have the *Lean* definition:
-/
lemma divides_def {d n : ℕ} : d ∣ n ↔ ∃ t, n = d * t
:= iff.rfl -- hide

/- Axiom : divides_def
d ∣ n ↔ ∃ t, n = d * t
-/


/-
The following useful lemma just says that any natural number divides
a multiple of itself, and its proof should just be one or two lines.
-/




/- Lemma :
Every natural number $k$ divides $k \cdot r$
-/
lemma divides_mul_left {k k' r : ℕ} : (k ∣ k') → k ∣ k' * r :=
begin
  intro h,
  cases h with s hs,
  use r * s,
  rw hs,
  ring,

  
end

lemma divides_mul_right {k k' r : ℕ} : (k ∣ k') → (k ∣ r * k') := by {rw mul_comm, exact divides_mul_left} -- hide

/- Axiom : divides_mul_right
k ∣ k' → k ∣ r * k'
-/