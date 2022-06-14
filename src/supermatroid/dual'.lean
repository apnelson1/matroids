
import .basic'
import .weak_compl

universes u v


namespace supermatroid

variables {α : Type u} [lattice α] 

section lattice_dual 

variable [is_modular_lattice α]

lemma middle_dual (M : supermatroid α) : @satisfies_middle_axiom αᵒᵈ _ M.basis :=
begin
    rintros x y b hb b' hb' hxy hxb hb'y,
    obtain ⟨b₀,hb₀,hyb₀,hb₀x⟩ := M.basis_middle y x b' hb' b hb hxy hb'y hxb, 
    exact ⟨b₀, hb₀, hb₀x, hyb₀⟩, 
end

-- relies on inf_basis_of and lt_basis_sup
--lemma max_inf_dual (M : supermatroid α) : @max_inf αᵒᵈ _ M.basis := M.basis_min_sup

lemma min_sup_dual (M : supermatroid α) : @min_sup αᵒᵈ _ M.basis := M.basis_max_inf

lemma min_sup_compl [has_precompl α] (M : supermatroid α) : min_sup (has_precompl.pcompl ⁻¹' M.basis) 
  :=
begin
  intros x b hb, 
  obtain ⟨b',hb', h1,h2⟩ := M.basis_max_inf xᵒ bᵒ hb, 
  refine ⟨b'ᵒ, sorry, _,_⟩ ,
end 
-- begin
--   show ∀ (x b: α) (hb : M.basis b), ∃ (b' : α) (hb': M.basis b'),
--      b ⊓ x ≤ b' ∧ ∀ (b'' : α) (hb'' : M.basis b''), b' ⊓ x ≤ b'' → b'' ⊓ x = b' ⊓ x, 

--   intros x b hb, 
--   obtain ⟨b₁, hxb₁, hb₁, hxxb₁⟩ := hb.sup_super_of x, 
--   refine ⟨b₁,hb₁, by rwa inf_comm at hxb₁, 
--     λ b₂ hb₂ hb₁b₂, inf_eq_inf_of_le_of_le (by_contra (λ hcon, _)) hb₁b₂⟩, 
  
--   set s := (x ⊓ b₂) ⊔ b₁ with hs_def, 

--   have hb₁s : b₁ < s := lt_of_le_of_ne le_sup_right 
--     (λ h_eq, hcon (by rwa [h_eq, eq_comm, sup_eq_right, inf_comm, ←h_eq] at hs_def)), 

--   obtain ⟨b₃, hb₃, hb₃s, hsb₃⟩ := hb₁.basis_inf_lt hb₁s hb₂, 
--   have h₁ := sup_lt_sup_of_lt_of_inf_le_inf hb₃s (_ : s ⊓ x ≤ b₃ ⊓ x), 
--   { refine hxxb₁.not_spanning_of_lt (lt_of_lt_of_le h₁ (sup_le _ le_sup_right)) le_sup_right 
--       (hb₃.sup_right_spanning _), 
--     rw [sup_comm, hs_def],
--     exact sup_le_sup_right inf_le_left _},
  
--   refine le_inf (le_trans (le_inf inf_le_left _) hsb₃) inf_le_right, 
--   rw [hs_def, sup_inf_assoc_of_le _ (inf_le_left : _ ≤ x), sup_le_iff], 
--   exact ⟨inf_le_right, hb₁b₂⟩, 
-- end 

/-- The `lattice_dual` of a supermatroid is the supermatroid on the dual order with the same
  set of bases -/
def lattice_dual (M : supermatroid α) : supermatroid (αᵒᵈ) :=  
{ basis := M.basis,
  exists_basis := M.exists_basis,
  basis_antichain := M.basis_antichain.to_dual,
  basis_middle := M.middle_dual,
  basis_max_inf := M.max_inf_dual,
  basis_min_sup := M.min_sup_dual, }

end lattice_dual 

section matroid_dual 

variable [has_precompl α]

lemma min_sup_of_max_inf_precompl (B : α → Prop) (h : max_inf B) (h' : @max_inf αᵒᵈ _ B) : 
  min_sup B := 
begin
  intros x b hb, 
  set y := (order_dual.to_dual xᵒ) with hy, 
  obtain ⟨b',hb',hb'b,hb'_max⟩ := h' y b hb, 
  --have := hb'_max b hb, 
  refine ⟨b',hb', _, _⟩, 

end 

def supermatroid_of_max_inf (B : α → Prop) (h_exists : ∃ b, B b) (h_antichain : is_antichain (≤) B)
  (h_middle : satisfies_middle_axiom B) (h_max_inf : max_inf B) : supermatroid α := 
{ basis := B,
  exists_basis := h_exists,
  basis_antichain := h_antichain,
  basis_middle := h_middle,
  basis_max_inf := h_max_inf,
  basis_min_sup := sorry  } 


end matroid_dual 

end supermatroid