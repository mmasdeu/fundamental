import tactic -- hide
import data.real.basic -- hide
/-
## The `split` tactic

Sometimes the goal is a conjunction of two statements. It may be directly a `∧` (it is typed with `\and`),
or it may be secretely a conjuntion, like an if and only if statement (since `↔` (type it with `\iff`)
means `→` and `←`). In those cases, the `split` tactic will produce two goals.

If you don't do anything afterwards, you will be working on the first of the goals until you solve them,
and then you will work on the second, and so on. It is nicer, however, to isolate them using `{}` to separate
the different blocks. Below you can see an example (notice the commas!).
-/

example (a b : ℕ) (h1 : a = 3) (h2 : b = 5) : a = 3 ∧ b = 5 :=
begin
  split,
  {
    assumption,
  },
  {
    assumption,
  }
end

/- Symbol :
∧ : \and
-/
/- Lemma : no-side-bar
For every $x,y\in \mathbb{Z}$, we have $(x+y)^2 = x^2 + 2xy + y^2$ and $(x-y)^2 = x^2 - 2xy + y^2$.
-/
lemma sp0 (x y : ℤ) : (x+y)^2 = x^2 + 2*x*y + y^2 ∧ (x-y)^2 = x^2 - 2*x*y + y^2 :=
begin
  split,
  {
    ring,
  },
  {
    ring,
  }


  
end