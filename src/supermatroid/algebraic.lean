import data.set.finite 
import order.upper_lower
import order.atoms  
import order.zorn

universes u v 

variables {α : Type u} [complete_lattice α] {S P C : set α} {a b x : α}

def is_compact (c : α) := 
  ∀ (S : set α), c ≤ Sup S → ∃ (F : set α), F ⊆ S ∧ set.finite F ∧ c ≤ Sup F 

class is_algebraic (α : Type u) [complete_lattice α] : Prop := 
  (is_Sup_compact : ∀ (x : α), x = Sup ({c : α | is_compact c ∧ c ≤ x}))

lemma chain_thing (hP : P.nonempty) (hcl : ∀ {x y}, x ∈ P → y ∈ P → x ⊔ y ∈ P )  
(h_chain : ∀ (C ⊆ P), is_chain (≤) C → Sup C ∈ P) : 
  Sup P ∈ P  := 
begin
  obtain ⟨⟨s,hs⟩,h',h⟩ := @zorn_preorder₀ P _ set.univ _, 
  { convert hs, refine (Sup_le (λ b hbP, _)).antisymm (le_Sup hs),
    { simpa using (h ⟨_, hcl hs hbP⟩ (set.mem_univ _))}},
  
  rintros C - hC, 
  specialize h_chain (coe '' C) _ (is_chain.image _ _ _ (by simp) hC),  
  { rintros x ⟨y,hy,rfl⟩, exact y.2},
  refine ⟨⟨_,h_chain⟩, ⟨set.mem_univ _, _⟩⟩, 
  rintros ⟨z,hz⟩ hzC,
  simp only [subtype.mk_le_mk], 
  exact le_Sup ⟨⟨z,hz⟩,hzC, rfl⟩, 
end 

lemma Inf_coatoms_eq_bot (α : Type u) [complete_lattice α] [is_coatomistic α] : 
  Inf {a : α | is_coatom a} = ⊥ :=
@Sup_atoms_eq_top αᵒᵈ _ _

lemma covby_chain_of_coatomistic [is_coatomistic α] (hC : is_chain (≤) C) (haC : a ∈ C) :
  ∃ z ∈ C, ∀ x ∈ C, x < Sup C → x ≤ z :=
begin
  by_contradiction h, 
  push_neg at h, 
  --obtain ⟨S, hCS, hS⟩ := eq_Inf_coatoms (Sup C), 
  have h_coatom : ∃ z, is_coatom z ∧ z ⊓ (Sup C) < Sup C,
  begin
    by_contradiction h₀, push_neg at h₀, 
    simp only [inf_lt_right, not_forall, exists_prop, not_exists, not_and, not_not] at h₀, 
    
    have := (@le_Inf_iff α _ {a : α | is_coatom a} (Sup C)).mpr h₀, 
    simp [(Inf_coatoms_eq_bot α)] at this, 
    have hC' : Sup C = ⊥ := by simpa,
    obtain ⟨x,-,hx,-⟩ := h _ haC, 
    rw hC' at hx, simpa using hx, 
  end, 
  obtain ⟨z,hz,hzC⟩ := h_coatom, 
  set C' := (λ m, z ⊓ m) '' C with hC', 
  
  --have := λ a (ha : a ∈ S), h (a ⊓ Sup C), 
end 

lemma chain_thing' (h : ∀ (a c : α), a < c → ∃ b, a ≤ b ∧ b ⋖ c) : 
  ∀ (C ⊆ P), is_chain (≤) C → C.nonempty →  Sup C ∈ P :=
begin
  rintros hC hCP hchain ⟨a,ha⟩, 
  refine by_contra (λ h', _), 
  have hlt := (le_Sup ha).lt_of_ne (by {rintro rfl, exact h' (hCP ha)}), 
  obtain ⟨b, hab, hbc⟩ := h _ _ hlt, 

  --obtain ⟨b,hab,hbP⟩ := h a c,
   
end 