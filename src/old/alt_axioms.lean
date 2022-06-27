import .dual 

universes u v
 


--def supermatroid.maximizable {α : Type u} [preorder α] (s : set α) : Prop := 
--  ∀ (a ∈ s) b, a ≤ b → (maximals (≤) ((set.Icc a b) ∩ s)).nonempty

--def supermatroid.augmentable {α : Type u} [semilattice_sup α] (s : set α) : Prop := 
--  ∀ (a ∈ s) b, (a ∉ maximals (≤) s) → (b ∈ maximals (≤) s) → ((set.Ioc a (a ⊔ b)) ∩ s).nonempty 

variables {α : Type u} [lattice α] [bounded_order α] {M : supermatroid α} 
  {i j b x y c d r : α}

open set supermatroid 

@[ext] structure supermatroid' (α : Type u) [semilattice_sup α] := 
(indep         : α → Prop)
(ind_nonempty  : ∃ x, indep x ) 
(ind_lower_set : is_lower_set indep)
(le_basis_sup  : ∀ i b, indep i → (maximals (≤) indep) b → 
  ∃ b', (maximals (≤) indep) b' ∧ i ≤ b' ∧ b' ≤ i ⊔ b) 
(ind_maximize' : ∀ x, (maximals (≤) ((Iic x) ∩ indep)).nonempty) 

def supermatroid'_of (M : supermatroid α) : supermatroid' α := { 
  indep         := M.indep,
  ind_nonempty  := M.ind_nonempty,
  ind_lower_set := M.ind_lower_set,
  le_basis_sup  := λ i b hi hb, hi.le_basis_sup hb,
  ind_maximize' := λ x, by {
    obtain ⟨i,hi⟩ := M.exists_basis_of x,
    exact ⟨i,⟨hi.le,hi.indep⟩,λ j hj hij, hi.eq_of_le_indep hij hj.1 hj.2⟩}}


lemma aug' (M : supermatroid' α): augmentable M.indep := 
begin
  intros i his b hi_nb hb, 
  obtain ⟨b',h₁,h₂,h₃⟩ := M.le_basis_sup i b his hb, 
  exact ⟨b', ⟨lt_of_le_of_ne' h₂ (λ h, hi_nb (h ▸ h₁)), h₃⟩, h₁.1⟩, 
end 

