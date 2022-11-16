import fibonacci_world.induction -- hide

/-
## The Fibonacci key lemma

Below is the definition of the Fibonacci sequence. Notice that we specify
what is $F_0$, what is $F_1$ and then we use a recurrence to define $F_{n+2}$.
-/

def Fib : ℕ → ℕ
| 0 := 0
| 1 := 1
| (n + 2) := Fib n + Fib (n+1)

/-
It is useful to have the first few values available, as well as a rule
to rewrite the recurrence. The proofs of the following lemmas are `by definition`,
this is what `rfl` means at the end of the lines.
-/
lemma Fib0 : Fib 0 = 0 := rfl
lemma Fib1 : Fib 1 = 1 := rfl
lemma Fib2 : Fib 2 = 1 := rfl
lemma Fib_def (n : ℕ) : Fib (n+2) = Fib n + Fib (n+1) := rfl

/-
Armed with these tools, prove this important lemma on Fibonacci numbers. Remember
the `induction'` lemma that you just proved!
-/

/- Lemma :
For all $k$ and $n$, we have $F_{n+k+1} = F_k F_n + F_{k+1} F_{n+1}$.
-/
lemma Fib_general (n k : ℕ) : Fib (n + k + 1) = (Fib k) * (Fib n) + (Fib (k+1)) * (Fib (n+1)) :=
begin
  apply induction' k,
  {
    rw Fib0,
    rw Fib1,
    ring,
  },
  {
    rw Fib1,
    rw Fib2,
    rw Fib_def,
    ring,
  },
  {
    intro k,
    intro h0,
    intro h1,
    rw show n+(k+2)+1 = (n+k+1)+2, by ring,
    rw Fib_def,
    rw show n + k + 1 + 1 = n + (k+1) + 1, by ring,
    rw h0,
    rw h1,
    rw Fib_def,
    rw Fib_def,
    rw Fib_def,
    ring,
  }








end
