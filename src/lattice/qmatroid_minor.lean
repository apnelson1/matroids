import .qmatroid

universes u v 

open set subtype 

variables {α : Type u}{a b : α} [qmatroid α]

section restriction 

instance : qmatroid (Iic a) := { 
  basis_sup := λ _ _ _, by simpa using qmatroid.basis_sup _ _ _,  

  basis_Sup_chain :=  
  begin
    rintros ⟨i,a⟩ C hC_chain hC_ne h,
    
    simp only [complete_lattice.Sup, mk_basis_iff], 
    simp only [mem_Iic, basis_Iic_iff_coe_basis_coe, coe_mk, set_coe.forall] at h,
    exact qmatroid.basis_Sup_chain i (coe '' C) 
      (by {rintros _ ⟨⟨x,hxa⟩,hx,rfl⟩ _ ⟨⟨y,hya⟩,hy,rfl⟩ hne,
        specialize hC_chain hx hy,
        simp only [coe_mk, ne.def, mk_le_mk] at hne ⊢ hC_chain,
        exact hC_chain (λ h_eq, hne (mk_eq_mk.mp h_eq))})      
      (by simpa) 
      (λ x ⟨⟨y,hy⟩, hyC, hyx⟩, by {rw ←hyx,exact h y hy hyC}),  
  end ,
  canopy_Inf_chain := 
  begin
    rintros ⟨s,a⟩ C hC_chain ⟨⟨x₀,hx₀a⟩, hx₀⟩ h,
    obtain ⟨h₀,h₀',h₀''⟩ := h _ hx₀,
    simp only [complete_lattice.Inf, canopy_for_iff, spanning_Iic_iff_exists_basis_le_coe, coe_mk, 
      mk_le_mk, forall_exists_index, and_imp, set_coe.forall, mk_eq_mk, mem_Iic] at ⊢ h₀, 
    refine ⟨h₀,inf_le_of_right_le _,_⟩, 
    { sorry},
    
  end ,
  ..(infer_instance : supermatroid (Iic a)) }

end restriction 