import .basic 

universes u v

section circuit

variables {α : Type u} {i j b b' b'' x y c d r s t : α}
[complete_lattice α] [is_atomistic α] [is_coatomistic α] {M : supermatroid α}

namespace supermatroid 

/-- A circuit is a minimal dependent element-/
def circuit (M : supermatroid α) : α → Prop := minimals (≤) M.indepᶜ 

/-- A cocircuit is a maximally nonspanning element-/
def cocircuit (M : supermatroid α) : α → Prop := maximals (≤) M.spanningᶜ

lemma circuit.not_indep (hc : M.circuit c) : ¬ M.indep c := hc.1 

lemma circuit.dep (hc : M.circuit c) : M.dep c := hc.1 

lemma circuit.indep_of_lt (hC : M.circuit c) (hiC : i < c) : M.indep i := 
  by_contra (λ h, hiC.ne.symm (hC.2 h hiC.le))

def cov_between (x a b : α) : Prop := a ⋖ x ∧ x ⋖ b

lemma foo {a b i i' j : α} (hii' : i ≠ i') (hi_dep : M.dep i) (hi'_dep : M.dep i') 
  (hi : cov_between i a b) (hi' : cov_between i' a b) (hj : cov_between j a b) : M.dep j := 
begin
  intro hj_ind, 
  have ha := hj_ind.indep_of_le hj.1.le, 
end  


lemma dep.exists_circuit_le (hx : M.dep x) : ∃ c, M.circuit c ∧ c ≤ x := 
begin
  obtain ⟨i,hi⟩ := M.exists_basis_of x, 
  
  obtain ⟨z, hzx, hzi, hzx⟩ := exists_atom_of_not_le (λ h, hx (hi.indep_of_le h)),
  


  set ps := {p | is_coatom p ∧ M.dep (p ⊓ (i ⊔ z))} with hps, 
  refine ⟨Inf ps, ⟨λ hpi, _ ,sorry⟩, le_of_le_forall_coatom (λ q hq hxq, _)⟩, 
  { },
  convert Inf_le _, 
  simp only [mem_set_of_eq, hps], 
  refine ⟨hq, hi.not_indep_of_lt 
    (lt_of_le_of_ne (le_inf (hi.le.trans hxq) le_sup_left) 
      (λ h, hzx (by {rw h, simp [hzi.trans hxq]}))) 
    (inf_le_of_right_le (sup_le hi.le hzi))⟩,  
  
  
  




  


  --set sc := {x ∈ si | M.indep (Sup ((si.insert z) \ {x}))}.insert z with hsc,
  
  --have hciz : Sup sc ≤ Sup (si.insert z) := Sup_le_Sup (insert_subset_insert (sep_subset _ _)),  
  
  -- refine ⟨Sup sc, ⟨λ (hci : M.indep (Sup sc)),_,_⟩,_⟩,  
  -- { obtain ⟨j,hj,hcj⟩ := hci.le_basis_of hciz, },
  
  
  
  
end 

end supermatroid 


end circuit