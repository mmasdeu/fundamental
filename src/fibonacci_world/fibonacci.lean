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
  {
    use 0,
    ring,
  },
  {
    apply induction k,
    {
      intros n hn,
      rw show 0 * (n+1) = 0, by ring,
    },
    {
      intros r hr n hn,
      cases hn with d hd,
      rw show (r + 1)*(n+1) = (r+1) * n + r + 1, by ring,
      rw Fib_general,
      apply divides_add,
      {
        use Fib ((r+1) * n + 1),
      },
      {
        use d * Fib r,
        rw hd,
        ring,
      }
    }
  }














end