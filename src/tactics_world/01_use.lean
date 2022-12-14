import tactic -- hide
open nat -- hide

/-
## The `use` tactic

The following tactic works on goals of the form "There exists $x$ such that...". So if the goal starts
with `∃`, to prove it you need to supply a value for $x$ and then prove that this value works. The first
part will be done with the `use x` (replace `x` with an actual value) and then the goal will
change into proving the required property of `x`.
-/

/- Symbol:
∃ : \exists
-/
/- Lemma : no-side-bar
There is a solution to $x^2+5 = 14$ in $\mathbb{N}$.
-/
lemma use0 : ∃ (x : ℕ), x^2 + 5 = 14 :=
begin
  use 3,
  ring,



  
end