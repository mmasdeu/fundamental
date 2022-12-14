import tactic -- hide

/-
## Sets and subsets in Lean

If `A, B, C` are declared to be sets, then we can state propositions such as `x ∈ A`, `A ⊆ B`, `A ⊂ B ∪ C` ...

For Lean `A ⊆ B` is the same as `∀ x, x ∈ A → x ∈ B`. Therefore:

- If the have a goal like `A ⊆ B` we can use `intro x` to change the goal to `x ∈ A → x ∈ B`.
- If we have `h: A ⊆ B` and we want to prove the goal `x ∈ B` we can use `apply` to change the goal to `x ∈ A`.
- If we have `h: A ⊆ B` and `hx: x ∈ A` we can use `specialize` to obtain a proof of `x ∈ B`.
-/

variables {X: Type} -- hide 

/- Lemma :
If $A \subseteq B$ and $B \subseteq C$, then $A \subseteq C$.
-/
lemma subset_transitivity {A B C: set X} (h1: A ⊆ B) (h2: B ⊆ C): A ⊆ C :=
begin
  intro x,
  intro h,
  apply h2,
  apply h1,
  assumption,
  
  

  
end