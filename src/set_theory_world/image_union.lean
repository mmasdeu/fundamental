import data.set.basic -- hide
import set_theory_world.image_tutorial
import tactic -- hide

/-

## The image of a union

In this level we prove that the image of a union of two sets if the union of their images.

In Lean, `x ∈ A ∪ B` is the same as `x ∈ A ∨ x ∈ B`, so the `left/right` tactics work in the goal, as well
as the `cases` one in a hypothesis.
-/

open set -- hide
variables{X Y: Type} -- hide

/- Lemma
$ f(A ∪ B) = f(A) ∪ f(B) $
-/
lemma image_union (f : X → Y) (A B : set X) : f '' (A ∪ B) = f '' A ∪ f '' B :=
begin
  ext y,
  split,
  {
    intro h1,
    cases h1,
    cases h1_h,
    cases h1_h_left,
    {
      left, 
      rw ← h1_h_right,
      use [h1_w, h1_h_left],
    },
    {
      right,
      rw  ← h1_h_right,
      use [h1_w, h1_h_left],
    },
  },
  {
    intro h1,
    cases h1,
    {
      cases h1,
      cases h1_h,
      rw ← h1_h_right,
      use h1_w,
      split,
      {
        left,
        assumption,
      },
      refl,
    },
    {
      cases h1,
      cases h1_h,
      rw ← h1_h_right,
      use h1_w,
      split,
      {
        right,
        assumption,
      },
      refl,
    },
  },







end
