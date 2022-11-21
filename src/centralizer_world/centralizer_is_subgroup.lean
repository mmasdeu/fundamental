import normalizer_world.normalizer_is_minimal -- hide

variables {G : Type} [group G] -- hide

/-
## The centralizer

In this world we prove two basic facts about centralizers. Here
is the definition of the centralizer of a subset $A$ of a given group $G$:
-/
@[reducible] -- hide
def centralizer (A : set G) := {g : G | ∀ a, a ∈ A → g*a*g⁻¹ = a }

/-
We can use the following lemma to rewrite using the definition.
-/
lemma centralizer_mem (A : set G) (g : G) :
g ∈ centralizer A ↔ ∀ a, a ∈ A → g * a * g⁻¹ = a
:= iff.rfl -- hide

/- Axiom: centralizer_mem
g ∈ centralizer A ↔ ∀ a, a ∈ A → g * a * g⁻¹ = a
-/

/-
The first goal is to prove that the centralizer of any set
is a subgroup.
-/

/- Lemma: no-side-bar
The centralizer $C_G(A)$ is a subgroup of $G$.
-/
lemma sc1 (A : set G) : subgroup (centralizer A) :=
begin
  rw subgroup,
  split,
  {
    use 1,
    rw centralizer,
    intro a,
    rw (show 1 * a * 1⁻¹ = a, by group),
    tauto,
  },
  {
    intros x y hx hy,
    rw centralizer_mem at hx hy ⊢,
    intros c hc,
    rw show x * y⁻¹ * c * (x * y⁻¹)⁻¹ = x * (y⁻¹ * c * y) * x⁻¹, by group,
    have hk : y⁻¹ * c * y = c,
    {
      specialize hy c hc,
      rw show y⁻¹ * c * y = y⁻¹ * (y * c * y⁻¹) * y, by rw hy,
      group,
    },
    rw hk,
    rw (hx c hc),
  }







  
end
