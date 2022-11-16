import tactic -- hide
open function -- hide
/-
## The Tutorial Boss

In this level we practice the previous concepts, using functions between sets.
The composition of two functions is written with ∘ (type it with `\circ`), and we
have available the definition of injective as well.
-/

variables {X Y Z : Type} {x : X} (f : X → Y) (g : Y → Z) -- hide

lemma comp_def : (g ∘ f) x = g (f x)
:= rfl -- hide

lemma injective_def : injective f ↔ ∀ x y, f x = f y → x = y
:= by unfold injective -- hide

/- Lemma : no-side-bar
If $g \circ f$ is injective, then $f$ is injective.
-/
lemma injective_comp
{X Y Z : Type} (f : X → Y) (g : Y → Z) :  --
injective (g ∘ f) → injective f :=
begin
  intro h,
  intro x,
  intro y,
  intro hxy,
  rw injective_def at h,
  apply h,
  rw comp_def,
  rw hxy,
end
