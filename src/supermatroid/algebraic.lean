import data.set.finite 
import order.upper_lower

universes u v 

variables {α : Type u} [complete_lattice α] {S : set α} {a : α}

def is_compact (c : α) := 
  ∀ (S : set α), c ≤ Sup S → ∃ (F : set α), F ⊆ S ∧ set.finite F ∧ c ≤ Sup F 

class is_algebraic (α : Type u) [complete_lattice α] : Prop := 
  (is_Sup_compact : ∀ (x : α), x = Sup ({c : α | is_compact c ∧ c ≤ x}))

-- this is BS 
lemma Sup_le_of_forall_sup_le [is_algebraic α] (hS : ∀ x ∈ S, x ≤ a) 
  (hcl : ∀ {x y}, x ≤ a → y ≤ a → x ⊔ y ≤ a) : 
  Sup S ≤ a := 
begin
   
  rw [is_algebraic.is_Sup_compact (Sup S), Sup_le_iff],   
  rintros c ⟨hc,hcS⟩, 
  obtain ⟨F,hFS,hF,hcF⟩ := hc S hcS, 
  refine hcF.trans _, revert hFS, 
  
  refine (hF.induction_on (by simp) _), 
  intros a T haT hT hTf haTS, 
  rw [set.insert_subset] at haTS, 
  rw [Sup_insert], 
  exact hcl (hS _ haTS.1) (hTf haTS.2), 
end 