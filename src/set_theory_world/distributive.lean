import data.set.basic -- hide
open set -- hide

/-
## The distributive property

The extensionality property of sets says that two sets are equal if and only if they have the same elements.

One can `apply ext, intro x` to invoke it. The `ext` tactic is a shortcut for this.
-/

variables {X Y : Type} -- hide

/- Lemma :
The distributive property of ∩ with respect to ∪.
-/
lemma inter_union (A B C : set X) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
begin
  ext,
  split,
  {
    intro h,
    cases h,
    cases h_right,
    {
      left,
      split;
      assumption,
    },
    {
      right,
      split;
      assumption,
    }
  },
  {
    intro h,
    cases h,
    {
      split,
      {
        exact h.1,
      },
      {
        left,
        exact h.2,
      },
    },
    {
      split,
      {
        exact h.1,
      },
      {
        right,
        exact h.2,
      }
    }
  }
end
