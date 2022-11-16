import subgroup_world.subgroup_mul -- hide

variables {G : Type} [group G] -- hide

/-
## The normalizer subgroup

In this level you need to prove that the normalizer of any subset $A \subseteq G$ is a subgroup of $G$.

Below you can see the definition of the normalizer, as a certain subset of $G$. You can use `normalizer_mem`
to `rw`rite the definition, if needed.
-/
@[reducible] -- hide
def normalizer  (A : set G) := {g : G | ∀ a, a ∈ A ↔ g*a*g⁻¹ ∈ A }

/- Axiom: normalizer (A : set G)
{g : G | ∀ a, a ∈ A ↔ g*a*g⁻¹ ∈ A }
-/

lemma normalizer_mem (A : set G) (g : G) : g ∈ normalizer A ↔ ∀ a, a ∈ A ↔ g*a*g⁻¹ ∈ A
:= iff.rfl -- hide

/- Axiom: normalizer_mem (A : set G)
g ∈ normalizer A ↔ ∀ a, a ∈ A ↔ g*a*g⁻¹ ∈ A
-/

/- Lemma: no-side-bar
The normalizer $N_G(A)$ is a subgroup of $G$.
-/
lemma sn1 {A : set G} : subgroup (normalizer A) :=
begin
  split,
  {
    use 1,
    rw normalizer_mem,
    intro a,
    rw (show 1 * a * 1⁻¹ = a, by group),
  },
  {
    intros x y hx hy,
    rw normalizer_mem at hx hy ⊢,
    intros c,
    split,
    {
      intros hc,
      rw show x * y⁻¹ * c * (x * y⁻¹)⁻¹ = x * (y⁻¹ * c * y) * x⁻¹, by group,
      specialize hy (y⁻¹ * c * y),
      rw (show y * (y⁻¹ * c * y) * y⁻¹ = c, by group) at hy,
      exact (hx (y⁻¹ * c * y)).1 (hy.2 hc),
    },
    {
      intro hc,
      rw (show x * y⁻¹ * c * (x * y⁻¹)⁻¹ = x * (y⁻¹ * c * y)* x⁻¹, by group) at hc,
      have : y⁻¹ * c * y ∈ A,
      {
        specialize hx (y⁻¹ * c * y),
        rw hx,
        assumption,
      },
      specialize hy (y⁻¹* c * y),
      rw (show c = y * (y⁻¹ * c * y) * y⁻¹, by group),
      rw ←hy,
      assumption,
    }
  }





  
end
