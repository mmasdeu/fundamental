import tactic -- hide
import data.real.basic -- hide

/-
## More on `cases`

What if we have a *disjunction* in an hypothesis? In this case, the proof usually
splits into two paths, one which assumes the left condition, and the other which assumes
the right one. This is also achieved with the `cases` tactic. If `h : P ∨ Q`, then
`cases h,` will produce two goals. In the first one, we will have `h : P` and in the second
`h : Q`.
-/

/- Lemma : no-side-bar
If $a = 3$ or $a = -3$, then $a^2=9$.
-/
lemma c2 (a : ℤ) (h : a = 3 ∨ a = -3) : a^2 = 9 :=
begin
  cases h,
  {
    rw h,
    ring,
  },
  {
    rw h,
    ring,
  }



end