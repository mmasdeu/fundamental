import tactic -- hide

/-
## Basic definition

Below we have one possible notion of being a subgroup. We will want to prove that
this definition matches the more natural one, and we will do so in this and the next levels.

Throughout, you will find very useful the `group` tactic, which works like the powerful `ring`
tactic but with equalities involving elements of a group.

You will need to type inverses, which are written using a superindex "-1". You type it as
`\-1`, and you will see how the `-1` appears as a superindex.
-/

variables {G : Type} [group G] {H : set G} -- hide

@[class] -- hide
def subgroup (X : set G) := X.nonempty ∧ (∀ x y, x ∈ X → y ∈ X → x * y⁻¹ ∈ X)

/- Axiom: subgroup (X : set G)
X.nonempty ∧ (∀ x y, x ∈ X → y ∈ X → x * y⁻¹ ∈ X)
-/

lemma nonempty_of_subgroup (X : set G) [h : subgroup X] : ∃ x, x ∈ X := h.1 -- hide

/- Axiom : nonempty_of_subgroup (X : set G) [subgroup X]
∃ x, x ∈ X
-/

lemma mul_inv_of_subgroup {X : set G} [h : subgroup X] {x y : G} (hx : x ∈ X) (hy : y ∈ X) : x * y⁻¹ ∈ X := h.2 x y hx hy -- hide

/- Axiom : mul_inv_of_subgroup {X : set G} [h : subgroup X] {x y : G}
(hx : x ∈ X) (hy : y ∈ X) :
x * y⁻¹ ∈ X
-/

/- Lemma:
If $H\leq G$, then $1 \in H$.
-/
lemma subgroup.one_mem [h : subgroup H]: (1 : G) ∈ H :=
begin
  cases h.1 with x hx,
  have h2 :=  h.2 x x hx hx,
  rw show (1 : G) = x * x⁻¹, by group,
  assumption,







end

