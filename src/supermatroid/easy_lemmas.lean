import tactic

universe u

section upper_lower

variables {α : Type u} [preorder α]

@[reducible] def lower_set_of (s : set α) : set α := {x | ∃ y ∈ s, x ≤ y}
@[reducible] def upper_set_of (s : set α) : set α := {x | ∃ y ∈ s, y ≤ x}

lemma upper_set_of_dual (s : set αᵒᵈ) : @upper_set_of αᵒᵈ _ s = @lower_set_of α _ s := rfl 
lemma lower_set_of_dual (s : set αᵒᵈ) : @lower_set_of αᵒᵈ _ s = @upper_set_of α _ s := rfl  

lemma set.Icc_dual' (x y : α) : @set.Icc αᵒᵈ _ x y = @set.Icc α _ y x := 
  by {ext, rw [set.mem_Icc, and_comm], refl}

lemma set.Icc_dual'' (x y : α) : @set.Icc αᵒᵈ _ x y = @set.Icc α _ y x := 
  set.ext (λ x, and_comm _ _)

lemma set.Icc_dual''' (x y : α) : @set.Icc αᵒᵈ _ x y = @set.Icc α _ y x := 
  set.dual_Icc 

end upper_lower

section lattice

variables {α : Type u} {a b x : α} [lattice α] 



lemma inf_le_inf_of_inf_le (h : a ⊓ x ≤ b) : a ⊓ x ≤ b ⊓ x := by simp [h]

lemma sup_le_sup_of_le_sup (h : a ≤ b ⊔ x) : a ⊔ x ≤ b ⊔ x := by simp [h]

lemma inf_eq_inf_of_le_of_le (h1 : a ⊓ x ≤ b) (h2 : b ⊓ x ≤ a) : a ⊓ x = b ⊓ x :=
  le_antisymm (inf_le_inf_of_inf_le h1) (inf_le_inf_of_inf_le h2)

lemma sup_eq_sup_of_le_of_le (h1 : a ≤ b ⊔ x) (h2 : b ≤ a ⊔ x) : a ⊔ x = b ⊔ x := 
  le_antisymm (sup_le_sup_of_le_sup h1) (sup_le_sup_of_le_sup h2)

end lattice 