import order.atoms
import .weak_compl

universe u

section upper_lower

open has_involution 

variables {α : Type u} [preorder α]

@[reducible] def lower_set_of (s : set α) : set α := {x | ∃ y ∈ s, x ≤ y}
@[reducible] def upper_set_of (s : set α) : set α := {x | ∃ y ∈ s, y ≤ x}

lemma lower_set_of_preimage_invo [has_involution α] (s : set α) : 
  lower_set_of (invo ⁻¹' s) = invo ⁻¹' (upper_set_of s) := 
begin
  ext x, simp only [set.mem_set_of_eq, set.mem_preimage, exists_prop],
  exact ⟨λ ⟨y,hy,hxy⟩, ⟨yᵒ, hy, invo_le_iff.mpr hxy⟩,
    λ ⟨y,hy,hxy⟩, ⟨yᵒ, (@invo_invo _ _ _ y).symm ▸ hy, le_invo_comm.mpr hxy⟩⟩, 
end 

lemma lower_set_of_image_invo [has_involution α] (s : set α) : 
  lower_set_of (invo '' s) = invo '' (upper_set_of s) := 
by rw [image_invo_eq_preimage_invo, lower_set_of_preimage_invo, image_invo_eq_preimage_invo]

lemma upper_set_of_image_invo [has_involution α] (s : set α) : 
  upper_set_of (invo '' s) = invo '' (lower_set_of s) :=
by {nth_rewrite 1 ←(invo_invo_image s), rw [lower_set_of_image_invo, invo_invo_image]}

lemma upper_set_of_preimage_invo [has_involution α] (s : set α): 
  upper_set_of (invo ⁻¹' s) = invo ⁻¹' (lower_set_of s) :=
by rw [←image_invo_eq_preimage_invo, ←image_invo_eq_preimage_invo, upper_set_of_image_invo]

lemma set.Icc_dual''' (x y : α) : @set.Icc αᵒᵈ _ x y = @set.Icc α _ y x := 
  set.dual_Icc 

end upper_lower

section lattice

variables {α : Type u} {a b x : α} [lattice α] 

lemma inf_le_inf_of_inf_le (h : a ⊓ x ≤ b) : a ⊓ x ≤ b ⊓ x := le_inf h inf_le_right 

lemma sup_le_sup_of_le_sup (h : a ≤ b ⊔ x) : a ⊔ x ≤ b ⊔ x := sup_le h le_sup_right

lemma inf_eq_inf_of_le_of_le (h1 : a ⊓ x ≤ b) (h2 : b ⊓ x ≤ a) : a ⊓ x = b ⊓ x :=
  (le_inf h1 inf_le_right).antisymm (le_inf h2 inf_le_right)

lemma sup_eq_sup_of_le_of_le (h1 : a ≤ b ⊔ x) (h2 : b ≤ a ⊔ x) : a ⊔ x = b ⊔ x := 
  (sup_le h1 le_sup_right).antisymm (sup_le h2 le_sup_right)


end lattice 

section atoms

class is_strongly_atomic (α : Type u) [preorder α] : Prop :=
(exists_left_covby_of_lt : ∀ (x y : α), x < y → ∃ a, x ⋖ a ∧ a ≤ y) 

class is_strongly_coatomic (α : Type u) [preorder α] : Prop :=
(exists_covby_right_of_lt : ∀ (x y : α), x < y → ∃ a, x ≤ a ∧ a ⋖ y)

--variables {α : Type u} [lattice α] [is_modular_lattice α]

instance {α : Type u} [preorder α] [is_strongly_atomic α] : is_strongly_coatomic αᵒᵈ :=
⟨ λ x y hxy, by {obtain ⟨a,hya,hax⟩ := @is_strongly_atomic.exists_left_covby_of_lt α _ _ y x hxy, 
    exact ⟨a,hax,covby.of_dual hya⟩}⟩ 

-- instance {α : Type u} : is_strongly_atomic (set α) :=
--   exists_covby_left

end atoms


