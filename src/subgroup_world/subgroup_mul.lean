import subgroup_world.subgroup_inv_bis -- hide

variables {G : Type} [group G] {H : set G} -- hide

/-
## Closed under product

Here you prove finally that the product of elements in a subgroup stays in the subgroup.
-/
/- Lemma:
If $H\leq G$, and $x, y \in H$, then $x y \in H$.
-/
lemma subgroup.mul_mem [h : subgroup H]
{x y : G} (hx : x ∈ H) (hy : y ∈ H) :  x * y ∈ H :=
begin
  rw show x * y = x * y⁻¹⁻¹, by group,
  apply h.2 _ _ hx (subgroup.inv_mem' hy),






end
