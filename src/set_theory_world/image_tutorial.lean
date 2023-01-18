import data.set.basic -- hide
import tactic -- hide

/-

## Working with the image of a function

In this level we will learn how to work with the image of a function.
If `A: set X` and `B: set Y` are sets and we have `f : X → Y`, the image of `A` under `f`, $ f(A) $ is written as `f '' A`.

If we have a proof that an element `b` belongs to the image, `hb: b ∈ f '' A` we can use `cases hb` to get a preimage and a proof that it belongs to the preimage.

```
hb_w : A
hb_h : hb_w ∈ A ∧ f hb_w = b
```

We can change the names using `cases hb with a ha` instead. Now we will get

```
a: A
ha: a ∈ A ∧ f a = b
```

If we want to prove something like `b ∈ f '' A`, we can use the `use` tactic to provide
an element `a : X`, and then prove that `a ∈ A` and `f a = b`.
-/

variables{X Y: Type} -- hide
variables {S : set X}
variables {y : Y}
variables {f : X → Y}

lemma mem_image : y ∈ f '' S ↔ ∃ x , x ∈ S ∧ f x = y
:= set.mem_image f S y
/- Axiom:
mem_image : y ∈ f '' S ↔ ∃ x , x ∈ S ∧ f x = y
-/


/- Lemma
If $ A ⊆ B $, then $ f(A) ⊆ f(B) $
-/
lemma image_subset (f : X → Y) (A B : set X) (h: A ⊆ B): f '' A ⊆  f '' B :=
begin
  intros y hy,
  cases hy with x hx,
  use x,
  split,
  apply h,
  exact hx.1,
  exact hx.2,

  

end