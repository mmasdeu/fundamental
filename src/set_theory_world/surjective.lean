import tactic -- hide
open function -- hide
/-
## Functions

Here we introduce the definition of a function being surjective,
and prove a "dual" version to the lemma from the previous level.
-/

variables {X Y Z : Type} {x : X} (f : X → Y) (g : Y → Z) -- hide

lemma surjective_def : surjective f ↔ ∀ y, ∃ x, f x = y
:= iff.rfl -- hide


/- Lemma : no-side-bar
If $g \circ f$ is surjective, then $g$ is surjective.
-/
lemma surjective_comp : 
surjective (g ∘ f) → surjective g :=
begin
  intro h,
  rw surjective_def at h ⊢,
  intro b,
  specialize h b,
  cases h with x hx,
  use f x,
  assumption,









end
