import subgroup_world.subgroup_one -- hide

variables {G : Type} [group G] {H : set G} -- hide

/-
## The inverse of an element is in the group

In this easy lemma you have to prove that the inverse of an element in a subgroup is in the
subgroup as well.
-/
/- Lemma:
If $H\leq G$, and $x \in H$, then $x^{-1} \in H$.
-/
lemma subgroup.inv_mem' [h : subgroup H] {x : G} (hg : x ∈ H) : x⁻¹ ∈ H :=
begin
  have h2 := h.2 (1 : G) x subgroup.one_mem hg,
  rw show (x⁻¹ = 1 * x⁻¹), by group,
  assumption,






end
