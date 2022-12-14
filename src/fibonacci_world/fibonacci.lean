import fibonacci_world.key  -- hide

/-
## The Final Boss

In this final level, you will prove that the Fibonacci number $F_k$ always divides $F_{kn}$,
for arbitrary natural numbers $k$ and $n$. You will need to use plain induction (`induction`), as well
as the key lemma `Fib_general` proved before.
-/

/- Lemma : no-side-bar
For all $k$ and $n$, $F_{k}$ divides $F_{kn}$.
-/
lemma final_boss (k n : ℕ) : Fib k ∣ Fib (k*n) :=
begin
  apply induction n,
  { -- simp works
    use 0,
    ring,
  },
  {
    apply induction k,
    { -- simp works
      intros n hn,
      rw show 0 * (n+1) = 0, by ring,
    },
    {
      intros r hr m hm,
      clear hr,
      rw show (r + 1)*(m + 1) = (r + 1) * m + r + 1, by ring,
      rw Fib_general,
      apply divides_add,
      {
        apply divides_mul_left,
      },
      {
        cases hm with d hd,
        rw hd,
        apply divides_mul_right,
        use d * Fib r,
        ring,
      }
    }
  }














end