import order.antichain

universes u v

open set 

class has_involution (α : Type u) [preorder α] :=
(invo' : α ≃o αᵒᵈ)
(is_involutive : ∀ x, invo' (invo' x) = x)

namespace has_involution

variables {α : Type u} {a b x y : α} {s : set α}

def invo [preorder α] [has_involution α] : (α → α) := λ a, invo' a 

postfix `ᵒ`:(max +1) := invo 

section preorder

variables [preorder α] [has_involution α] 
 
@[simp] lemma invo_invo (x : α) : xᵒᵒ = x := is_involutive x
lemma invo_le_iff : xᵒ ≤ yᵒ ↔ y ≤ x := invo'.le_iff_le
lemma invo_le (hxy : x ≤ y) : yᵒ ≤ xᵒ :=  invo_le_iff.2 hxy
lemma le_of_invo_le (hx : xᵒ ≤ yᵒ) : y ≤ x := 
  by {rw [←invo_invo y, ←invo_invo x], exact invo_le hx}
lemma le_invo_comm : x ≤ yᵒ ↔ y ≤ xᵒ := by rw [←invo_le_iff, invo_invo]
lemma invo_le_comm : xᵒ ≤ y ↔ yᵒ ≤ x := by rw [←invo_le_iff, invo_invo]
lemma invo_inj {x y : α} (h : xᵒ = yᵒ) : x = y := invo'.injective h

lemma invo_lt_iff : xᵒ < yᵒ ↔ y < x := by {apply @order_iso.lt_iff_lt α αᵒᵈ}
lemma lt_invo_comm : x < yᵒ ↔ y < xᵒ := by rw [←invo_lt_iff, invo_invo]
lemma invo_lt_comm : xᵒ < y ↔ yᵒ < x := by rw [←invo_lt_iff, invo_invo]

lemma image_invo_eq_preimage_invo : invo '' s = invo ⁻¹' s := 
ext (λ x, ⟨by {rintro ⟨x',hx',rfl⟩, rwa [←invo_invo x'] at hx'}, λ h, ⟨xᵒ, ⟨h, invo_invo x⟩⟩⟩) 

@[simp] lemma invo_invo_image : invo '' (invo '' s) = s := 
by {rw image_invo_eq_preimage_invo, apply invo'.to_equiv.preimage_image _}

lemma mem_image_invo {x : α} {s : set α} : x ∈ invo '' s ↔ xᵒ ∈ s := 
by {rw image_invo_eq_preimage_invo, refl}

lemma mem_image_invo' {x : α} {P : α → Prop} : (invo '' P) x ↔ P xᵒ := mem_image_invo 

lemma mem_preimage_invo' {x : α} {P : α → Prop} : (invo ⁻¹' P) x ↔ P xᵒ := 
by rw [←image_invo_eq_preimage_invo, mem_image_invo']

lemma image_antichain (hs : is_antichain (≤) s) : is_antichain (≤) (invo '' s) :=
begin
  rintros _ ⟨a,has, rfl⟩ _ ⟨b,hbs,rfl⟩ hab hle, 
  exact hs hbs has (λ h, hab (by rw h)) (invo_le_iff.mp hle),  
end 

lemma preimage_antichain (hs : is_antichain (≤) s) : is_antichain (≤) (invo ⁻¹' s) := 
λ a ha b hb hab hle, hs hb ha (λ h, hab (invo_inj h.symm)) (invo_le_iff.mpr hle)

@[simp] lemma preimage_Icc : invo ⁻¹' (Icc x y) = Icc yᵒ xᵒ := 
set.ext (λ x, by {simp only [mem_preimage, mem_Icc], rw [and_comm, invo_le_comm, le_invo_comm]})

@[simp] lemma preimage_Iic : invo ⁻¹' (Iic x) = Ici xᵒ := 
set.ext (λ a, by simpa only [mem_preimage, mem_Iic, mem_Ici] using invo_le_comm)

@[simp] lemma preimage_Ici : invo ⁻¹' (Ici x) = Iic xᵒ :=
set.ext (λ a, by simpa only [mem_preimage, mem_Iic, mem_Ici] using le_invo_comm)

@[simp] lemma image_Icc : invo '' (Icc x y) = Icc yᵒ xᵒ := 
by rw [image_invo_eq_preimage_invo, preimage_Icc]

@[simp] lemma image_Iic : invo '' (Iic x) = Ici xᵒ :=
by rw [image_invo_eq_preimage_invo, preimage_Iic]

@[simp] lemma image_Ici : invo '' (Ici x) = Iic xᵒ :=
by rw [image_invo_eq_preimage_invo, preimage_Ici]

end preorder 

section lattice 

variables [lattice α] [has_involution α]

lemma invo_sup : (a ⊔ b)ᵒ = aᵒ ⊓ bᵒ := @order_iso.map_sup α αᵒᵈ _ _ _ _ _
lemma invo_inf : (a ⊓ b)ᵒ = aᵒ ⊔ bᵒ := @order_iso.map_inf α αᵒᵈ _ _ _ _ _ 

end lattice 

section boolean_algebra

variables [boolean_algebra α]

instance of_boolean_algebra : has_involution α := ⟨order_iso.compl α, compl_compl⟩

lemma invo_eq_compl (x : α): xᵒ = xᶜ := rfl  

end boolean_algebra 

end has_involution



