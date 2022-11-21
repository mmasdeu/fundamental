import data.real.basic -- hide
/-
## The `ring` tactic

In this level we learn a high-level tactic, `ring`, which tries to prove a goal that involves
an algebraic expression (in any ring). Let's see it in action, it's quite powerful!
-/

/- Lemma : no-side-bar
For every $x,y,z\in \mathbb{Z}$, we have
$$(x+y)^3 - z^2 + 2xz - x^2 = x^3 + 3x^2y + 3xy^2 + y^3 - (z-x)^2$$.
-/
lemma r0 (x y z : ℤ) : (x+y)^3 - z^2 + 2*x*z - x^2 = x^3 + 3*x^2*y + 3*x*y^2 + y^3 - (z-x)^2 :=
begin
  ring,




end