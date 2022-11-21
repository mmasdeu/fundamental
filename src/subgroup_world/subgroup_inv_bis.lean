import subgroup_world.subgroup_inv -- hide

variables {G : Type} [group G] {H : set G} -- hide

/-
## The inverse of an element is in the group (II)

The following variation is useful because since it is an `↔` statement, it can be `rw`ritten.
-/

/- Lemma:
If $H\leq G$, then $x \in H$ if and only if $x^{-1} \in H$.
-/
lemma subgroup.inv_mem  [h : subgroup H] (x : G) : x ∈ H ↔ x⁻¹ ∈ H :=
begin
  split,
  {
    apply subgroup.inv_mem',
  },
  {
    intro hg,
    rw show x = x⁻¹⁻¹, by group,
    apply subgroup.inv_mem',
    assumption,
  }






end
