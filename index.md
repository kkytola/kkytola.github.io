## Welcome

Some info here.

## Links

Link to [publications] and [about].

## Pictures

Can we put pictures here?

## Formatted text

```lean
lemma compl_frontier {γ : Type*} [topological_space γ] (A : set γ) :
  (frontier A)ᶜ = (interior A) ∪ (interior (Aᶜ)) :=
begin
  have fact := @closure_eq_compl_interior_compl γ _ Aᶜ , 
  rw compl_compl at fact ,
  suffices : frontier A = (interior A)ᶜ ∩ (interior (Aᶜ))ᶜ ,
  { rw this ,
    rw compl_inter (interior A)ᶜ (interior (Aᶜ))ᶜ ,
    repeat {rw compl_compl ,} , } , 
  rw [←frontier_compl A , ←fact] ,
  exact diff_eq (closure (Aᶜ)) (interior (Aᶜ)) ,
end
```
