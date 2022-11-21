import tactic -- hide
open function nat -- hide

/-
## The `assumption` tactic

The first tactic that we'll learn is the `assumption` tactic. This can be used
when your goal is exactly one of your hypotheses. In the following example,
there are three hypotheses, namely the fact that $a$ is $3$ (hypothesis `ha`), the
fact that $b$ is $4$ (hypothesis `hb`) and the fact that $c$ is $5$ (hypothesis `hc`).

Since we want to prove that $b=4$, which is one of our hypotheses, we should be able to
win by typing `assumption,` (**don't forget the comma**). Delete the `sorry` and try it.

**Pro tip:** If the hypothesis to be used is called, say `hb`, you can also close the goal
by using `exact hb,` instead. Sometimes it is more efficient to do so, especially if we believe
that assumption should work and we don't know why. The `exact` tactic will give us information
about why that does not work.

-/

/- Lemma : no-side-bar
If $a$ is $3$ and $b$ is $4$ and $c$ is $5$, then $b$ is $4$.
-/
lemma l0 (a b c : ℕ) (ha : a = 3) (hb : b = 4) (hc : c = 5) : b = 4 :=
begin
  assumption,

  
end
