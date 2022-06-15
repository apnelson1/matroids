
import .basic'
import .weak_compl

universes u v

/-
lemma basis.exists_extension_from (hb : M.basis b) (x : α) : 
  ∃ b', b' ≤ x ⊔ b ∧ M.basis b' ∧ (M.basis_of (b' ⊓ x) x) :=

  M.basis_of i x ↔ i ≤ x ∧ 
    ∃ b, B b ∧ i ≤ b ∧ ∀ b', B b' → i ≤ b' ⊓ x → b' ⊓ x = i

  M.basis_of (b ⊓ x) x ↔ 
    ∀ b', B b' → b ⊓ x ≤ b' → b ⊓ x = b' ⊓ x
-/


open set 

-- lemma bar {α : Type u} {i x : α} [partial_order α] (B : α → Prop) (h_ne : ∃ b, B b) 
--   (h_ac : is_antichain (≤) B) (h_mid : middle B) (h_ml : max_lower B) :
--   ∃ j, i ≤ j ∧ M.basis_of j x := 
-- begin
--   obtain ⟨b,hb,hbi⟩ := hi, 
--   obtain ⟨b',⟨hb',hb'x,hb'_max⟩⟩ := hb.max_inf x, 
--   refine ⟨b' ⊓ x, le_inf ((le_inf hbi hix).trans hb'x) hix, hb'.inf_right_indep _,inf_le_right, _⟩, 
--   rintros j ⟨b'',hb'',hjb''⟩ hjx hb'j, 
--   have h₀ := (le_inf hjb'' hjx), 
--   rw [←(hb'_max _ hb'' (hb'j.trans hjb''))] at h₀, 
--   exact le_antisymm hb'j h₀, 
-- end 

namespace supermatroid

--example 



variables {α : Type u} [lattice α] [is_modular_lattice α]

lemma foo (M : supermatroid α) : min_upper M.basis := 
begin
  rintros x y ⟨s,⟨b,hb,hbs⟩,hxs,hsy⟩, 
  obtain ⟨b₁,hb₁b,hb₁,hb₁x⟩ := hb.inf_basis_of x, 
  refine ⟨x ⊔ b₁,⟨⟨b₁,hb₁,le_sup_right⟩,le_sup_left,sup_le (hxs.trans hsy) 
    (hb₁b.trans ((sup_le hxs hbs).trans hsy))⟩, _⟩, 
  
  rintros t ⟨⟨b₂,hb₂,hb₂t⟩,hxt,hty⟩ htx,  
  refine le_antisymm (sup_le hxt _) htx,
  by_contradiction hb₁t, 
  set j := b₁ ⊓ (x ⊔ b₂) with hj, 

  have hj_lt : j < b₁ := inf_le_left.lt_of_ne 
    (λ h_eq, hb₁t (by {rw ← h_eq, exact inf_le_right.trans (sup_le hxt hb₂t)})), 

  obtain ⟨b₃, hb₃, hjb₃, hb₃j⟩ := hb₁.lt_basis_sup hj_lt hb₂, 
  
  have h1 := @inf_lt_inf_of_lt_of_sup_le_sup _ _ _ _ _ x hjb₃ (sup_le_sup_of_le_sup _), 
  swap, 
  { rw [hj, inf_comm, inf_sup_assoc_of_le b₁ le_sup_right, le_inf_iff] at hb₃j, 
    rw [hj, inf_comm, inf_sup_assoc_of_le b₁ le_sup_left, le_inf_iff], 
    refine ⟨hb₃j.1, hb₃j.2.trans (sup_le le_sup_left (hb₂t.trans _))⟩,
    rwa sup_comm},
  refine (hb₁x.not_indep_of_lt (lt_of_le_of_lt (inf_le_inf_of_inf_le _) h1) 
    inf_le_right (hb₃.inf_right_indep x)), 
  rw [hj, inf_comm, @inf_comm _ _ _ (x ⊔ b₂)], 
  exact inf_le_inf_of_inf_le (inf_le_left.trans le_sup_left),  
end 



variable [is_modular_lattice α]


-- section matroid_dual 

-- variable [has_precompl α]

-- lemma min_sup_of_max_inf_precompl (B : α → Prop) (h : max_inf B) (h' : @max_inf αᵒᵈ _ B) : 
--   min_sup B := 
-- begin
--   intros x b hb, 
--   set y := (order_dual.to_dual x) with hy, 
--   obtain ⟨b',hb',hb'b,hb'_max⟩ := h' y b hb, 
--   --have := hb'_max b hb, 
--   refine ⟨b',hb', _, _⟩, 

-- end 

-- def supermatroid_of_max_inf (B : α → Prop) (h_exists : ∃ b, B b) (h_antichain : is_antichain (≤) B)
--   (h_middle : satisfies_middle_axiom B) (h_max_inf : max_inf B) : supermatroid α := 
-- { basis := B,
--   exists_basis := h_exists,
--   basis_antichain := h_antichain,
--   basis_middle := h_middle,
--   basis_max_inf := h_max_inf,
--   basis_min_sup := sorry  } 


-- end matroid_dual 

end supermatroid