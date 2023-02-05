import set_theory_world.image_Union -- hide
open function -- hide
open_locale big_operators -- hide
/-
## The preimage of a function

Given a function `f : X → Y`, the preimage of a subset $B ⊆ Y$ is written
as `f⁻¹' B`. We will also need to refer to $X$ as a subset of itself. It is
called `univ` in Lean. The following lemma is very well known.
-/
variables{X Y: Type} -- hide
variables {B : set Y}
variables {x : X} -- hide
variables {f : X → Y} -- hide

lemma mem_preimage : x ∈ f ⁻¹' B ↔ f x ∈ B
:= set.mem_preimage

/- Axiom:
mem_preimage : x ∈ f ⁻¹' B ↔ f x ∈ B
-/

/- Lemma
The image of the preimage of a set $B$ is $B ∩ \textrm{Im}(f)$.
-/
lemma image_preimage (B : set Y) :
f '' (f⁻¹' B ) = B ∩ f '' set.univ :=
begin
  ext y,
  split,
  {
    intro h,
    rw mem_image at h,
    obtain ⟨x, ⟨hx1, hx2⟩⟩ := h,
    rw mem_preimage at hx1,
    dsimp,
    split,
    {
      rw ←hx2,
      assumption,
    },
    {
      use x,
      split,
      {
        apply set.mem_univ,
      },
      {
        assumption,
      }
    }
  },
  {
    intro h,
    cases h with h1 h2,
    obtain ⟨x, ⟨hx1, hx2⟩⟩ := h2,
    use x,
    split,
    {
      rw mem_preimage,
      rw hx2,
      assumption,
    },
    {
      assumption,
    }
  }
end
