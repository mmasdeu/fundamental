import normalizer_world.normalizer_is_subgroup -- hide

variables {G : Type} [group G] -- hide

def is_normal (N H : set G) := N ⊆ H ∧ ∀ g n, g ∈ H → n ∈ N → g⁻¹ * n * g ∈ N

/- Axiom: is_normal (N H : set G)
N ⊆ H ∧ ∀ g n, g ∈ H → n ∈ N → g⁻¹ * n * g ∈ N
-/

/- Lemma: no-side-bar
If $H \leq G$, then $H$ is a normal subgroup of the normalizer $N_G(H)$.
-/
lemma sn2 (H : set G) [subgroup H] : is_normal H (normalizer H) :=
begin
  rw is_normal,
  rw normalizer,
  split,
  {
    intros h hH a,
    split,
    {
      intro ha,
      apply subgroup.mul_mem,
      {
        apply subgroup.mul_mem hH ha,
      },
      {
        rw ←subgroup.inv_mem,
        assumption,
      }
    },
    {
      intro ha,
      have hH' : h⁻¹ ∈ H,
      {
        rw ← subgroup.inv_mem,
        assumption,
      },
      rw show a = (h⁻¹ * (h * a * h⁻¹)) * h, by group,
      apply subgroup.mul_mem,
      apply subgroup.mul_mem hH' ha,
      assumption,
    }
  },
  {
    intros h n hG nh,
    rw hG (h⁻¹ * n * h),
    rw show h * (h⁻¹ * n * h) * h⁻¹ = n, by group,
    assumption,
  }












  
end