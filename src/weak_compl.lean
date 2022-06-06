import tactic 
import order.antichain

universes u v

open set 

class has_reverser (α : Type u) [preorder α] :=
(opp' : α ≃o αᵒᵈ)
(is_involutive : ∀ x, opp' (opp' x) = x)

namespace has_reverser

variables {α : Type u} {a b x y : α} {s : set α}

def opp [preorder α] [has_reverser α] : (α → α) := λ a, opp' a 

postfix `ᵒ` : (max + 1) := opp

section preorder

variables [preorder α] [has_reverser α] 

@[simp] lemma opp_opp (x : α) : xᵒᵒ = x := is_involutive x
lemma opp_le_iff : xᵒ ≤ yᵒ ↔ y ≤ x := opp'.le_iff_le
lemma opp_le (hxy : x ≤ y) : yᵒ ≤ xᵒ :=  opp_le_iff.2 hxy
lemma le_of_opp_le (hx : xᵒ ≤ yᵒ) : y ≤ x := by {rw [←opp_opp y, ←opp_opp x], exact opp_le hx}
lemma le_opp_comm : x ≤ yᵒ ↔ y ≤ xᵒ := by rw [←opp_le_iff, opp_opp]
lemma opp_le_comm : xᵒ ≤ y ↔ yᵒ ≤ x := by rw [←opp_le_iff, opp_opp]
lemma opp_inj {x y : α} (h : xᵒ = yᵒ) : x = y := opp'.injective h

lemma opp_lt_iff : xᵒ < yᵒ ↔ y < x := by {apply @order_iso.lt_iff_lt α αᵒᵈ}
lemma lt_opp_comm : x < yᵒ ↔ y < xᵒ := by rw [←opp_lt_iff, opp_opp]
lemma opp_lt_comm : xᵒ < y ↔ yᵒ < x := by rw [←opp_lt_iff, opp_opp]

lemma image_eq_preimage : opp '' s = opp ⁻¹' s := 
ext (λ x, ⟨by {rintro ⟨x',hx',rfl⟩, rwa [mem_preimage, opp_opp]}, λ h, ⟨xᵒ, ⟨h, opp_opp x⟩⟩⟩) 

lemma mem_image {x : α} {s : set α} : x ∈ opp '' s ↔ xᵒ ∈ s := by {rw image_eq_preimage, refl}

lemma image_antichain (hs : is_antichain (≤) s) : is_antichain (≤) (opp '' s) :=
begin
  rintros _ ⟨a,has, rfl⟩ _ ⟨b,hbs,rfl⟩ hab hle, 
  exact hs hbs has (λ h, hab (by rw h)) (opp_le_iff.mp hle),  
end 

lemma preimage_antichain (hs : is_antichain (≤) s) : is_antichain (≤) (opp ⁻¹' s) := 
λ a ha b hb hab hle, hs hb ha (λ h, hab (opp_inj h.symm)) (opp_le_iff.mpr hle)

end preorder 

section lattice 

variables [distrib_lattice α] [has_reverser α]

lemma opp_sup : (a ⊔ b)ᵒ = aᵒ ⊓ bᵒ := @order_iso.map_sup α αᵒᵈ _ _ _ _ _
lemma opp_inf : (a ⊓ b)ᵒ = aᵒ ⊔ bᵒ := @order_iso.map_inf α αᵒᵈ _ _ _ _ _ 

end lattice 

end has_reverser



