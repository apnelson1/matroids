import order.antichain

universes u v

open set 

class has_precompl (α : Type u) [preorder α] :=
(compl' : α ≃o αᵒᵈ)
(is_involutive : ∀ x, compl' (compl' x) = x)

namespace has_precompl

variables {α : Type u} {a b x y : α} {s : set α}

def pcompl [preorder α] [has_precompl α] : (α → α) := λ a, compl' a 

postfix `ᵒ`:(max +1) := pcompl 

section preorder

variables [preorder α] [has_precompl α] 
 
@[simp] lemma pcompl_pcompl (x : α) : xᵒᵒ = x := is_involutive x
lemma pcompl_le_iff : xᵒ ≤ yᵒ ↔ y ≤ x := compl'.le_iff_le
lemma pcompl_le (hxy : x ≤ y) : yᵒ ≤ xᵒ :=  pcompl_le_iff.2 hxy
lemma le_of_pcompl_le (hx : xᵒ ≤ yᵒ) : y ≤ x := 
  by {rw [←pcompl_pcompl y, ←pcompl_pcompl x], exact pcompl_le hx}
lemma le_pcompl_comm : x ≤ yᵒ ↔ y ≤ xᵒ := by rw [←pcompl_le_iff, pcompl_pcompl]
lemma pcompl_le_comm : xᵒ ≤ y ↔ yᵒ ≤ x := by rw [←pcompl_le_iff, pcompl_pcompl]
lemma pcompl_inj {x y : α} (h : xᵒ = yᵒ) : x = y := compl'.injective h

lemma pcompl_lt_iff : xᵒ < yᵒ ↔ y < x := by {apply @order_iso.lt_iff_lt α αᵒᵈ}
lemma lt_pcompl_comm : x < yᵒ ↔ y < xᵒ := by rw [←pcompl_lt_iff, pcompl_pcompl]
lemma pcompl_lt_comm : xᵒ < y ↔ yᵒ < x := by rw [←pcompl_lt_iff, pcompl_pcompl]

lemma image_pcompl_eq_preimage_pcompl : pcompl '' s = pcompl ⁻¹' s := 
ext (λ x, ⟨by {rintro ⟨x',hx',rfl⟩, rwa [←pcompl_pcompl x'] at hx'}, λ h, ⟨xᵒ, ⟨h, pcompl_pcompl x⟩⟩⟩) 

@[simp] lemma pcompl_pcompl_image : pcompl '' (pcompl '' s) = s := 
by {rw image_pcompl_eq_preimage_pcompl, apply compl'.to_equiv.preimage_image _}

lemma mem_image_pcompl {x : α} {s : set α} : x ∈ pcompl '' s ↔ xᵒ ∈ s := by {rw image_pcompl_eq_preimage_pcompl, refl}

lemma image_antichain (hs : is_antichain (≤) s) : is_antichain (≤) (pcompl '' s) :=
begin
  rintros _ ⟨a,has, rfl⟩ _ ⟨b,hbs,rfl⟩ hab hle, 
  exact hs hbs has (λ h, hab (by rw h)) (pcompl_le_iff.mp hle),  
end 

lemma preimage_antichain (hs : is_antichain (≤) s) : is_antichain (≤) (pcompl ⁻¹' s) := 
λ a ha b hb hab hle, hs hb ha (λ h, hab (pcompl_inj h.symm)) (pcompl_le_iff.mpr hle)

end preorder 

section lattice 

variables [lattice α] [has_precompl α]

lemma pcompl_sup : (a ⊔ b)ᵒ = aᵒ ⊓ bᵒ := @order_iso.map_sup α αᵒᵈ _ _ _ _ _
lemma pcompl_inf : (a ⊓ b)ᵒ = aᵒ ⊔ bᵒ := @order_iso.map_inf α αᵒᵈ _ _ _ _ _ 

end lattice 

section boolean_algebra

variables [boolean_algebra α]

instance of_boolean_algebra : has_precompl α := ⟨order_iso.compl α, compl_compl⟩

lemma pcompl_eq_compl (x : α): xᵒ = xᶜ := rfl  

end boolean_algebra 

end has_precompl



