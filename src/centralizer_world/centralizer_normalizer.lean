import centralizer_world.centralizer_is_subgroup -- hide

variables {G : Type} [group G] -- hide

/-
## The Final Boss

In this very final level we will prove that $C_G(A)$ is a normal subgroup
of $N_G(A)$. This takes a bit of effort, but hopefully the tools
that you have learned all along the way will serve you well in this
final battle. Good luck!
-/
/- Lemma: no-side-bar
The centralizer $C_G(A)$ is a normal subgroup of the normalizer $N_G(A)$.
-/
lemma sc2 (A : set G) : is_normal (centralizer A) (normalizer A) :=
begin
  rw is_normal,
  split,
  {
    intro x,
    intro hx,
    rw normalizer_mem,
    rw centralizer_mem at hx,
    intro a,
    split,
    {
      intro ha,
      specialize hx a ha,
      rw hx,
      assumption,
    },
    {
      intro ha,
      specialize hx _ ha,
      rw mul_left_inj (x⁻¹) at hx,
      rw mul_right_inj x at hx,
      rw ←hx,
      assumption,
    }
  },
  {
    intros g x hg hx,
    rw normalizer_mem at hg,
    rw centralizer_mem at hx ⊢,
    intros a ha,
    replace hg := (hg a).1 ha,
    specialize hx _ hg,
    rw show g⁻¹ * x * g * a * (g⁻¹ * x * g)⁻¹ = g⁻¹ * (x * (g * a * g⁻¹) * x⁻¹) * g, by group,
    rw hx,
    group,
  }
end