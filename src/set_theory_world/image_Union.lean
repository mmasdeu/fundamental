import set_theory_world.image_union -- hide
open function -- hide
open_locale big_operators -- hide
/-
## Indexed unions

In this level we learn how to work with arbitrary indexed unions. These are made
of an index set, and a function `A : I → set X`, that picks a subset of `A i` of `X` for
each index `i : I`.

The defining property of the union is given by the following lemma:
-/

/- Symbol :
∪ : \cup
∩ : \cap
⋃ : \Union
⋂ : \Inter
-/
variables {X Y I : Type} -- hide
variables {A : I → set X}
variable {x : X}

lemma mem_Union : (x ∈ ⋃ i, A i) ↔ ∃ i, x ∈ A i :=
set.mem_Union -- hide

/- Lemma : 
The image of an arbitrary union of sets is the union of the images.
-/
lemma image_Union  (f : X → Y) (A : I → set X) :
f '' ( ⋃ i, A i ) = ⋃ i, f '' (A i) :=
begin
  ext y,
  split,
  {
    intro h,
    obtain ⟨x, ⟨hx1, hx2⟩⟩ := h,
    rw set.mem_Union at hx1,
    obtain ⟨j, hj⟩ := hx1,
    rw mem_Union,
    use j,
    use x,
    split; assumption,
  },
  {
    intro h,
    rw mem_Union at h,
    obtain ⟨i, hi⟩ := h,
    obtain ⟨x, ⟨hx1, hx2⟩⟩ := hi,
    use x,
    rw mem_Union,
    split,
    {
      use i,
      assumption,
    },
    {
      assumption,
    }
  }








end
