import normalizer_world.normalizer_is_normal -- hide

variables {G : Type} [group G] -- hide

/- Lemma: no-side-bar
If $H \leq K$ is a normal subgroup, then $K \leq N_G(H)$.
-/
lemma sn3 (H K : set G) [subgroup H]  [subgroup K]  (hHK : is_normal H K) :
K ⊆ normalizer H :=
begin
  intro k,
  intro hk,
  rw normalizer,
  intro x,
  cases hHK,
  split,
  {
    intro hx,
    specialize hHK_right k⁻¹ x,
    rw subgroup.inv_mem at hk,
    rw show k * x * k⁻¹ = k⁻¹⁻¹ * x * k⁻¹, by group,
    apply hHK_right hk hx,
  },
  {
    intro hx,
    specialize hHK_right k (k * x * k⁻¹) hk hx,
    rw show x = k⁻¹ * (k * x * k⁻¹) * k, by group,
    assumption,
  }








  
end