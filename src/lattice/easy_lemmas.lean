import order.atoms

import data.finite.basic 
import order.hom.complete_lattice


universes u v

variables {α : Type u} {β : Type v}

section upper_lower


variables [preorder α] {x y z a b: α}

@[reducible] def lower_closure (s : set α) : set α := {x | ∃ y ∈ s, x ≤ y}
@[reducible] def upper_closure (s : set α) : set α := {x | ∃ y ∈ s, y ≤ x}

-- lemma lower_closure_preimage_invo [has_involution α] (s : set α) : 
--   lower_closure (invo ⁻¹' s) = invo ⁻¹' (upper_closure s) := 
-- begin
--   ext x, simp only [set.mem_set_of_eq, set.mem_preimage, exists_prop],
--   exact ⟨λ ⟨y,hy,hxy⟩, ⟨yᵒ, hy, invo_le_iff.mpr hxy⟩,
--     λ ⟨y,hy,hxy⟩, ⟨yᵒ, (@invo_invo _ _ _ y).symm ▸ hy, le_invo_comm.mpr hxy⟩⟩, 
-- end 

-- lemma lower_closure_image_invo [has_involution α] (s : set α) : 
--   lower_closure (invo '' s) = invo '' (upper_closure s) := 
-- by rw [image_invo_eq_preimage_invo, lower_closure_preimage_invo, image_invo_eq_preimage_invo]

-- lemma upper_closure_image_invo [has_involution α] (s : set α) : 
--   upper_closure (invo '' s) = invo '' (lower_closure s) :=
-- by {nth_rewrite 1 ←(@invo_invo_image _ s), rw [lower_closure_image_invo, invo_invo_image]}

-- lemma upper_closure_preimage_invo [has_involution α] (s : set α): 
--   upper_closure (invo ⁻¹' s) = invo ⁻¹' (lower_closure s) :=
-- by rw [←image_invo_eq_preimage_invo, ←image_invo_eq_preimage_invo, upper_closure_image_invo]

-- lemma set.Icc_dual''' (x y : α) : @set.Icc αᵒᵈ _ x y = @set.Icc α _ y x := 
--   set.dual_Icc 

end upper_lower

section covby

variables [partial_order α] {x y z a b : α}

lemma covby.eq_of_le_of_lt (hab : a ⋖ b) (hax : a ≤ x) (hxb : x < b) : a = x :=
by_contra (λ h, hab.2 (hax.lt_of_ne h) hxb)

lemma covby.eq_of_lt_of_le (hab : a ⋖ b) (hax : a < x) (hxb : x ≤ b) : x = b :=
by_contra (λ h, hab.2 hax (hxb.lt_of_ne h))

lemma covby.eq_or_of_le_of_le (hab : a ⋖ b) (hax : a ≤ x) (hxb : x ≤ b) : x = a ∨ x = b :=
begin
  obtain ⟨rfl, hax⟩ := em (a = x), 
    exact or.inl rfl, 
  exact or.inr ((hab.eq_of_lt_of_le (hax.lt_of_ne h)) hxb), 
end 

lemma wcovby.covby_or_eq (hab : a ⩿ b) : a ⋖ b ∨ a = b := wcovby_iff_covby_or_eq.mp hab

end covby



section lattice

variables [lattice α]  {x y z a b: α}

lemma inf_le_inf_of_inf_le (h : a ⊓ x ≤ b) : a ⊓ x ≤ b ⊓ x := le_inf h inf_le_right 

lemma sup_le_sup_of_le_sup (h : a ≤ b ⊔ x) : a ⊔ x ≤ b ⊔ x := sup_le h le_sup_right

lemma inf_eq_inf_of_le_of_le (h1 : a ⊓ x ≤ b) (h2 : b ⊓ x ≤ a) : a ⊓ x = b ⊓ x :=
  (le_inf h1 inf_le_right).antisymm (le_inf h2 inf_le_right)

lemma sup_eq_sup_of_le_of_le (h1 : a ≤ b ⊔ x) (h2 : b ≤ a ⊔ x) : a ⊔ x = b ⊔ x := 
  (sup_le h1 le_sup_right).antisymm (sup_le h2 le_sup_right)

end lattice 

section modular

variables [lattice α] [is_modular_lattice α] {x y z a b: α}

lemma eq_of_le_of_inf_le_of_sup_le' (hxy : x ≤ y) (hinf : y ⊓ z ≤ x) (hsup : y ≤ x ⊔ z) : x = y :=
eq_of_le_of_inf_le_of_sup_le hxy (le_inf hinf inf_le_right) (sup_le hsup le_sup_right) 

lemma inf_coatom_wcovby [order_top α] (x : α) (ha : is_coatom a) : x ⊓ a ⩿ x := 
begin
  by_cases hxa : x ≤ a, 
  { rw inf_eq_left.mpr hxa, exact rfl.wcovby}, 
  refine covby.wcovby ⟨inf_le_left.lt_of_ne (λ h, hxa (inf_eq_left.mp h)), λ y hxy hyx, hyx.ne _⟩,  
  refine @eq_of_le_of_inf_le_of_sup_le' _ _ _ _ _ a hyx.le hxy.le _, 
  rw ha.2 (y ⊔ a) (le_sup_right.lt_of_ne (λ hay, _)), 
  exact le_top, 
  rw [eq_comm, sup_eq_right] at hay, 
  exact (lt_of_lt_of_le hxy (le_inf hyx.le hay)).ne rfl,
end 

lemma sup_atom_wcovby [order_bot α] (x : α) (ha : is_atom a) : x ⩿ x ⊔ a := 
(@inf_coatom_wcovby αᵒᵈ _ _ _ _ _ ha).to_dual  

lemma sup_atom_covby_of_not_le [order_bot α] {x a : α} (ha : is_atom a) (hx : ¬ a ≤ x) : 
  x ⋖ x ⊔ a :=
(sup_atom_wcovby x ha).covby_of_ne (λ h, hx (sup_eq_left.mp h.symm))

lemma inf_coatom_covby_of_not_le [order_top α] {x a : α} (ha : is_coatom a) (hx : ¬ x ≤ a) : 
  x ⊓ a ⋖ x :=
(@sup_atom_covby_of_not_le αᵒᵈ _ _ _ x a ha hx).to_dual

end modular

section atoms

variables [complete_lattice α] [is_atomistic α] {x y z a b : α}

lemma le_of_forall_atom_le (h : ∀ a, is_atom a → a ≤ x → a ≤ y) : x ≤ y :=
by {obtain ⟨sx,rfl,hsx⟩ := eq_Sup_atoms x, exact Sup_le (λ b hb, h b (hsx b hb) (le_Sup hb))} 
  
lemma le_iff_forall_atom_le : x ≤ y ↔ (∀ a, is_atom a → a ≤ x → a ≤ y) := 
⟨λ hxy a ha hax, hax.trans hxy, le_of_forall_atom_le⟩

lemma eq_of_atom_le_iff_atom_le (h : ∀ a, is_atom a → (a ≤ x ↔ a ≤ y)) : x = y := 
(le_of_forall_atom_le (λ a ha, (h a ha).mp)).antisymm (le_of_forall_atom_le (λ a ha, (h a ha).mpr))

lemma exists_atom_of_not_le (hxy : ¬ (x ≤ y)) : ∃ a, is_atom a ∧ a ≤ x ∧ ¬ (a ≤ y) :=
by_contra (λ h, hxy (le_of_forall_atom_le (by {push_neg at h, exact h}))) 

lemma exists_atom_of_lt (hxy : x < y) : ∃ a, is_atom a ∧ a ≤ y ∧ ¬ (a ≤ x) :=
exists_atom_of_not_le (not_le_of_lt hxy)

lemma exists_atom_le_of_ne_bot (hx : x ≠ ⊥) : ∃ a, is_atom a ∧ a ≤ x := 
by {obtain ⟨a,ha,hax,-⟩ := exists_atom_of_lt (bot_le.lt_of_ne' hx), exact ⟨a,ha,hax⟩}

lemma covby.exists_atom_sup (hxy : x ⋖ y) : ∃ a, is_atom a ∧ y = x ⊔ a := 
begin
  obtain ⟨a,ha,hxa,hay⟩ := exists_atom_of_lt hxy.lt, 
  exact ⟨a, ha, (hxy.eq_of_lt_of_le (le_sup_left.lt_of_not_le (by simpa)) 
    (sup_le hxy.le hxa)).symm⟩,    
end 

lemma exists_sup_atom_of_inf_coatom_of_ne_bot [is_modular_lattice α] {x a : α} (hx : x ≠ ⊥) 
(ha : is_coatom a) : 
  ∃ b, is_atom b ∧ x = (x ⊓ a) ⊔ b := 
begin
  obtain ⟨b,hb,hbx⟩ := exists_atom_le_of_ne_bot hx,
  exact or.elim (inf_coatom_wcovby x ha).covby_or_eq (λ h, h.exists_atom_sup) 
    (λ h, ⟨b, hb, by rw [h, sup_eq_left.mpr hbx]⟩),
end 


end atoms

section coatoms

variables [complete_lattice α] [is_coatomistic α] {x y z a : α}

lemma le_of_le_forall_coatom (h : ∀ a, is_coatom a → y ≤ a → x ≤ a) : x ≤ y :=
@le_of_forall_atom_le αᵒᵈ _ _ _ _ h
  
lemma le_iff_le_forall_coatom : x ≤ y ↔ (∀ a, is_coatom a → y ≤ a → x ≤ a) := 
@le_iff_forall_atom_le αᵒᵈ_ _ _ _

lemma eq_of_le_coatom_iff_le_coatom (h : ∀ a, is_coatom a → (x ≤ a ↔ y ≤ a)) : x = y := 
@eq_of_atom_le_iff_atom_le αᵒᵈ _ _ _ _ h

lemma exists_coatom_of_not_le (hxy : ¬ (x ≤ y)) : ∃ a, is_coatom a ∧ y ≤ a ∧ ¬ (x ≤ a) :=
@exists_atom_of_not_le αᵒᵈ _ _ _ _ hxy  

lemma exists_coatom_of_lt (hxy : x < y) : ∃ a, is_coatom a ∧ x ≤ a ∧ ¬ (y ≤ a) :=
@exists_atom_of_lt αᵒᵈ _ _ _ _ hxy

lemma exists_le_coatom_of_ne_top (hx : x ≠ ⊤) : ∃ b, is_coatom b ∧ x ≤ b := 
@exists_atom_le_of_ne_bot αᵒᵈ _ _ _ hx 

lemma covby.exists_coatom_inf (hxy : x ⋖ y): ∃ a, is_coatom a ∧ x = y ⊓ a :=
@covby.exists_atom_sup αᵒᵈ _ _ _ _ hxy.to_dual 

lemma exists_inf_coatom_of_sup_atom_of_ne_top [is_modular_lattice α] {x a : α} (hx : x ≠ ⊤) 
(ha : is_atom a): 
  ∃ b, is_coatom b ∧ x = (x ⊔ a) ⊓ b := 
@exists_sup_atom_of_inf_coatom_of_ne_bot αᵒᵈ _ _ _ _ _ hx ha

end coatoms 

section finite

variables [finite α] 

instance : finite αᵒᵈ := (infer_instance : finite α)

lemma finite.exists_maximal' [nonempty α] [preorder α] : ∃ x : α, ∀ y, ¬ (x < y) :=
begin
  haveI := fintype.of_finite α, 
  exact (finset.univ.exists_maximal finset.univ_nonempty).imp 
    (λ a h y hay, (exists.elim h (λ _ h', h' _ (finset.mem_univ _) hay))), 
end 

lemma finite.exists_minimal' [nonempty α] [preorder α] : ∃ x : α, ∀ y, ¬ (y < x) :=
@finite.exists_maximal' αᵒᵈ _ _ _ 

lemma set.finite.exists_maximal_mem' [preorder α] {s : set α} (hs : s.nonempty) : 
  ∃ x ∈ s, ∀ y, y ∈ s → ¬ (x < y) := 
begin
  obtain ⟨⟨x,hx⟩,h⟩ :=  @finite.exists_maximal' s _ hs.to_subtype _, 
  exact ⟨x,hx,λ y hy, λ hlt, h ⟨y,hy⟩ (subtype.mk_lt_mk.mpr hlt)⟩,
end 

lemma set.finite.exists_minimal_mem' [preorder α] {s : set α} (hs : s.nonempty) : 
  ∃ x ∈ s, ∀ y, y ∈ s → ¬ (y < x) := 
@set.finite.exists_maximal_mem' αᵒᵈ _ _ _ hs

lemma set.finite.exists_maximal_mem [partial_order α] {s : set α} (hs : s.nonempty) : 
  ∃ x ∈ s, ∀ y, y ∈ s → x ≤ y → x = y := 
(set.finite.exists_maximal_mem' hs).imp 
  (λ x h, h.imp (λ hxs hx y hys hxy, eq_of_le_of_not_lt hxy (hx _ hys)))

lemma set.finite.exists_minimal_mem [partial_order α] {s : set α} (hs : s.nonempty) : 
  ∃ x ∈ s, ∀ y, y ∈ s → y ≤ x → y = x := 
(set.finite.exists_minimal_mem' hs).imp 
  (λ x h, h.imp (λ hxs hx y hys hxy, eq_of_le_of_not_lt hxy (hx _ hys)))


end finite 

section complete 

variables [complete_lattice α] {a : α} {S T : set α} {f : α → α}

lemma Sup_image_sup_left_eq_sup_Sup_of_nonempty (hS : S.nonempty) : 
  Sup ((λ x, a ⊔ x) '' S) = a ⊔ (Sup S) := 
let ⟨x,hx⟩ := hS in
(Sup_le (by {rintro _ ⟨y,hy,rfl⟩, refine sup_le_sup_left (le_Sup hy) _, })).antisymm 
  (sup_le (le_sup_left.trans (le_Sup ((set.mem_image _ _ _).mpr ⟨x,hx,rfl⟩))) 
  (Sup_le_Sup_of_forall_exists_le (λ y hy, ⟨a ⊔ y, ⟨⟨y,hy,rfl⟩,le_sup_right⟩⟩)))

lemma Sup_image_sup_right_eq_Sup_sup_of_nonempty (hS : S.nonempty) : 
  Sup ((λ x, x ⊔ a) '' S) = (Sup S) ⊔ a := 
by {rw [sup_comm, ←Sup_image_sup_left_eq_sup_Sup_of_nonempty hS], simp_rw [sup_comm]}
   
lemma Inf_image_inf_right_eq_Inf_inf_of_nonempty (hS : S.nonempty) : 
  Inf ((λ x, x ⊓ a) '' S) = (Inf S) ⊓ a := 
@Sup_image_sup_right_eq_Sup_sup_of_nonempty αᵒᵈ _ _ _ hS 
  
lemma Inf_image_inf_left_eq_inf_Inf_of_nonempty (hS : S.nonempty) : 
  Inf ((λ x, a ⊓ x) '' S) = a ⊓ (Inf S) := 
@Sup_image_sup_left_eq_sup_Sup_of_nonempty αᵒᵈ _ _ _ hS 

-- these are already in mathlib : supr_sup etc . Maybe PR the below?

lemma bsupr_eq_supr_subtype : 
  (⨆ (x : α) (H : x ∈ S), f x) = ⨆ (y : ↥S), f y :=
supr_subtype'  
 
lemma bsupr_sup (hS : S.nonempty) : 
  (⨆ (x ∈ S), (f x ⊔ a)) = (⨆ (x ∈ S), f x) ⊔ a := 
by {simpa [supr_subtype'] using (@supr_sup _ _ _ hS.to_subtype _ _).symm} 

lemma sup_bsupr (hS : S.nonempty) : 
  (⨆ (x ∈ S), (a ⊔ f x)) = a ⊔ (⨆ (x ∈ S), f x) := 
by {rw [sup_comm, ←bsupr_sup hS], simp_rw [sup_comm]}

lemma binf_inf (hS : S.nonempty) : 
  (⨅ (x ∈ S), (f x ⊓ a)) = (⨅ (x ∈ S), f x) ⊓ a :=
@bsupr_sup αᵒᵈ _ _ _ _ hS
  
lemma inf_binf (hS : S.nonempty) : 
  (⨅ (x ∈ S), (a ⊓ f x)) = a ⊓ (⨅ (x ∈ S), f x) :=
@sup_bsupr αᵒᵈ _ _ _ _ hS

lemma Inf_diff_singleton_inf_of_mem_eq (ha : a ∈ S) : (Inf (S \ {a})) ⊓ a = Inf S :=
begin
  nth_rewrite 1 ←(Inf_singleton : Inf {a} = a), 
  rw [←Inf_union, set.diff_union_of_subset (set.singleton_subset_iff.mpr ha)], 
end 

lemma Sup_diff_singleton_sup_of_mem_eq (ha : a ∈ S) : (Sup (S \ {a})) ⊔ a = Sup S :=
@Inf_diff_singleton_inf_of_mem_eq αᵒᵈ _ _ _ ha

lemma supr_bool_eq' {f : bool → α} (i : bool) : (⨆ j, f j) = f i ⊔ f (!i) := 
by {rw supr_bool_eq, cases i; simp [sup_comm]}

lemma infi_bool_eq' {f : bool → α} (i : bool) : (⨅ j, f j) = f i ⊓ f (!i) := 
@supr_bool_eq' αᵒᵈ _ _ _



end complete 

section intervals

open set subtype 

instance [complete_lattice α] {a : α} : complete_lattice (Iic a) := 
{ Sup := λ S, ⟨_, (Sup_le (λ _ ⟨⟨_,hb⟩,_,rfl⟩, hb) : complete_lattice.Sup (coe '' S) ≤ a)⟩,
  Inf := λ S, ⟨_, @inf_le_left _ _ a (complete_lattice.Inf (coe '' S))⟩,
  le_Sup := λ _ _ h, coe_le_coe.mp (le_Sup (mem_image_of_mem _ h)),
  Sup_le := λ _ _ h, coe_le_coe.mp (Sup_le (by {rintros y ⟨z,p,rfl⟩, exact coe_le_coe.mpr (h z p)})),
  Inf_le := λ _ x h, coe_le_coe.mp (inf_le_of_right_le (Inf_le ⟨x,h,rfl⟩)), 
  le_Inf := λ _ x h, coe_le_coe.mp (le_inf x.2 
  (le_Inf (by {rintros _ ⟨z,p,rfl⟩, exact coe_le_coe.mpr (h z p)}))),
  .. (infer_instance : lattice (set.Iic a)),
  .. (infer_instance : bounded_order (set.Iic a)) }

instance [complete_lattice α] {a : α} : complete_lattice (Ici a) := 
{ Sup := λ S, ⟨_, (@le_sup_left _ _ a (complete_lattice.Sup (coe '' S)))⟩,
  Inf := λ S, ⟨complete_lattice.Inf (coe '' S), (le_Inf (λ _ ⟨⟨_,hb⟩,_,rfl⟩, hb))⟩,
  Inf_le := λ _ _ h, coe_le_coe.mp (Inf_le (mem_image_of_mem _ h)),
  le_Inf := λ _ _ h, coe_le_coe.mp (le_Inf (by {rintros _ ⟨z,p,rfl⟩, exact coe_le_coe.mpr (h z p)})),
  le_Sup := λ _ x h, coe_le_coe.mp (le_sup_of_le_right (le_Sup ⟨x,h,rfl⟩)), 
  Sup_le := λ _ x h, coe_le_coe.mp  
    (sup_le x.2 (Sup_le (by {rintros _ ⟨z,p,rfl⟩, exact coe_le_coe.mpr (h z p)}))),
  .. (infer_instance : lattice (set.Ici a)),
  .. (infer_instance : bounded_order (set.Ici a)) }

@[reducible] def Icc_complete_lattice [complete_lattice α] {a b : α} (hab : a ≤ b) : 
  complete_lattice (Icc a b) := 
{ Sup := λ S, ⟨a ⊔ Sup (coe '' S), 
    ⟨le_sup_left, sup_le hab (Sup_le (by {rintros _ ⟨⟨_,h⟩,_,rfl⟩, exact h.2}))⟩ ⟩,
  Inf := λ S, ⟨b ⊓ Inf (coe '' S), 
    ⟨le_inf hab (le_Inf (by {rintros _ ⟨⟨_,h⟩,_,rfl⟩, exact h.1})), inf_le_left⟩⟩, 
  Inf_le := λ _ x h, coe_le_coe.mp (inf_le_of_right_le (Inf_le (⟨x,h,rfl⟩))),
  le_Inf := λ _ x h, coe_le_coe.mp 
    (le_inf x.2.2 (le_Inf (by {rintros _ ⟨z,p,rfl⟩, exact coe_le_coe.mpr (h z p)}))),
  le_Sup := λ _ x h, coe_le_coe.mp (le_sup_of_le_right (le_Sup ⟨x,h,rfl⟩)), 
  Sup_le := λ _ x h, 
    (sup_le x.2.1 (Sup_le (by {rintros _ ⟨z,p,rfl⟩, exact coe_le_coe.mpr (h z p)}))),
  .. (infer_instance : lattice (set.Icc a b)),
  .. (Icc.bounded_order hab) }

@[simp] lemma set.Iic.coe_Sup [complete_lattice α] {a : α} {S : set (Iic a)} : 
  ((Sup S : Iic a) : α) = Sup ((coe : Iic a → α) '' S) := rfl 

@[simp] lemma set.Iic.coe_Inf [complete_lattice α] {a : α} {S : set (Iic a)} : 
  ((Inf S : Iic a) : α) = a ⊓ Inf ((coe : Iic a → α) '' S) := rfl 

lemma set.Iic.coe_Inf_nonempty_eq [complete_lattice α] {a : α} {S : set (Iic a)} (hS : S.nonempty) :
  ((Inf S : Iic a) : α) = Inf ((coe : Iic a → α) '' S) := by 
{ rw [set.Iic.coe_Inf, inf_eq_right], 
  exact exists.elim hS (λ ⟨x,hxa⟩ hx, le_trans (Inf_le (⟨⟨x,hxa⟩,hx,rfl⟩)) hxa)}

@[simp] lemma set.Iic.coe_sup [semilattice_sup α] {a : α} {x y : Iic a} : 
  (↑(x ⊔ y) : α) = (↑x ⊔ ↑y) := rfl 

@[simp] lemma set.Iic.coe_inf [semilattice_inf α] {a : α} {x y : Iic a} : 
  (↑(x ⊓ y) : α) = (↑x ⊓ ↑y) := rfl 

@[simp] lemma set.Ici.coe_inf [semilattice_inf α] {a : α} {x y : Iic a} : 
  (↑(x ⊓ y) : α) = (↑x ⊓ ↑y) := rfl 

@[simp] lemma set.Ici.coe_sup [semilattice_sup α] {a : α} {x y : Iic a} : 
  (↑(x ⊔ y) : α) = (↑x ⊔ ↑y) := rfl 

@[simp] lemma set.Icc.coe_inf [semilattice_inf α] {a : α} {x y : Iic a} : 
  (↑(x ⊓ y) : α) = (↑x ⊓ ↑y) := rfl 

@[simp] lemma set.Icc.coe_sup [semilattice_sup α] {a : α} {x y : Iic a} : 
  (↑(x ⊔ y) : α) = (↑x ⊔ ↑y) := rfl 

@[simp] lemma set.Ioc.coe_inf [semilattice_inf α] {a : α} {x y : Iic a} : 
  (↑(x ⊓ y) : α) = (↑x ⊓ ↑y) := rfl 

@[simp] lemma set.Ioc.coe_sup [semilattice_sup α] {a : α} {x y : Iic a} : 
  (↑(x ⊔ y) : α) = (↑x ⊔ ↑y) := rfl 

@[simp] lemma set.Ico.coe_inf [semilattice_inf α] {a : α} {x y : Iic a} : 
  (↑(x ⊓ y) : α) = (↑x ⊓ ↑y) := rfl 

@[simp] lemma set.Ico.coe_sup [semilattice_sup α] {a : α} {x y : Iic a} : 
  (↑(x ⊔ y) : α) = (↑x ⊔ ↑y) := rfl 

-- etc etc... PR this? 

-- @[simp, norm_cast] lemma coe_inf [semilattice_inf α] {P : α → Prop}
--   (Psup : ∀⦃x y⦄, P x → P y → P (x ⊓ y)) (x y : subtype P) :
-- (@has_inf.inf _ (@semilattice_inf.to_has_inf _ (subtype.semilattice_inf Psup)) x y : α)
--   = x ⊓ y := rfl

@[simp, norm_cast] lemma subtype.coe_sup [semilattice_sup α] {P : α → Prop}
(Psup : ∀⦃x y⦄, P x → P y → P (x ⊔ y)) (x y : subtype P) :
(@has_sup.sup _ (@semilattice_sup.to_has_sup _ (subtype.semilattice_sup Psup)) x y : α)
  = x ⊔ y := rfl

@[simp, norm_cast] lemma subtype.coe_inf [semilattice_inf α] {P : α → Prop}
(Pinf : ∀⦃x y⦄, P x → P y → P (x ⊓ y)) (x y : subtype P) :
(@has_inf.inf _ (@semilattice_inf.to_has_inf _ (subtype.semilattice_inf Pinf)) x y : α)
  = x ⊓ y := rfl

@[simp] lemma subtype.mk_sup [semilattice_sup α] {P : α → Prop}
(Psup : ∀⦃x y⦄, P x → P y → P (x ⊔ y)) {x y : α} (hx : P x) (hy : P y) :
(@has_sup.sup _ (@semilattice_sup.to_has_sup _ (subtype.semilattice_sup Psup)) ⟨x,hx⟩ ⟨y,hy⟩) =
  ⟨x ⊔ y, Psup hx hy⟩ := rfl

@[simp] lemma subtype.mk_inf [semilattice_inf α] {P : α → Prop}
(Pinf : ∀⦃x y⦄, P x → P y → P (x ⊓ y)) {x y : α} (hx : P x) (hy : P y) :
(@has_inf.inf _ (@semilattice_inf.to_has_inf _ (subtype.semilattice_inf Pinf)) ⟨x,hx⟩ ⟨y,hy⟩) =
  ⟨x ⊓ y, Pinf hx hy⟩ := rfl


end intervals 
