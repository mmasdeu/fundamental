import fibonacci_world.divides  -- hide
open function set

/-
## A stronger induction principle

We will will use the following basic induction principle, which is
already provided to us by *Lean*, to prove a stronger induction principle,
where the induction hypothesis is about the two previous values.

-/

variables {P : ℕ → Prop} -- hide
lemma induction  (n : ℕ) (h0 : P 0) (h : ∀ n, P n → P (n+1)) : P n
:= nat.rec h0 h n -- hide

/- Axiom : induction
(n : ℕ) (h0 : P 0) (h : ∀ n, P n → P (n+1)) : P n
-/

/-  Lemma :
If $P$ is a predicate on natural numbers, to prove $P(n)$ for all $n$
it suffices to show:

* $P(0)$,
* $P(1)$, and
* $\forall n, P(n) ∧ P (n+1)$ implies $P(n+2)$.
-/
lemma induction' {P : ℕ → Prop} (n : ℕ) 
(h : ∀ n, (P n → P (n+1) → P (n+2))) (h0 : P 0) (h1 : P 1) : P n :=
begin
  have h : ∀ n, P n ∧ P (n+1),
  {
    intro n,
    apply induction n,
    split,
    {
      assumption,
    },
    {
      assumption,
    },
    intros n hd,
    cases hd,
    split,
    {
      assumption,
    },
    {
      apply h,
      assumption,
      assumption,
    },
  },
  {
    cases h n,
    assumption,
  },














end