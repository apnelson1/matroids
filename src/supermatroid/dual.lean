/-
Copyright (c) 2022 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Peter Nelson.
-/
import .basic 
import .weak_compl

/-!
# supermatroids 

Given a `supermatroid` in a modular lattice with `has_precompl`, we define its dual. 

## Main content

-- `supermatroid.dual` : the dual supermatroid of a supermatroid `M`; its bases are the 
--   precomplements of the bases of `M`. 
-- `dual_dual`    : duality is idempotent. 

## References


TODO : rank, circuits, theory for finite supermatroids, etc etc. -/



universes u v

variables {α : Type u} [lattice α] [is_modular_lattice α] [bounded_order α] [has_precompl α] 
  {M : supermatroid α} {i j b x y c d r : α}

open has_precompl set 
namespace supermatroid 

def coindep (M : supermatroid α) (i : α) : Prop := ∃ (b : α), (M.basis b ∧ i ≤ bᵒ)

def cobasis (M : supermatroid α) : α → Prop := maximals (≤) M.coindep

lemma cobasis_iff : M.cobasis b ↔ b ∈ maximals (≤) M.coindep := iff.rfl 

lemma cobases_eq_image_pcompl_bases (M : supermatroid α) : 
  M.cobasis = pcompl '' M.basis := 
begin
  convert (image_antichain M.basis_antichain).max_lower_set_of, 
  simp only [cobasis, coindep, mem_image, exists_prop, exists_exists_and_eq_and],
  refl, 
end 

lemma coindep_iff (M : supermatroid α) : 
   M.coindep x ↔ ∃ b, (M.basis b ∧ x ≤ bᵒ) := iff.rfl  

lemma cobasis_iff_pcompl_basis (M : supermatroid α) :
  M.cobasis b ↔ M.basis bᵒ  :=
by rw [cobases_eq_image_pcompl_bases, mem_image_pcompl'] 

lemma bot_coindep (M : supermatroid α) : M.coindep ⊥ := 
M.coindep_iff.mpr (exists.elim (M.exists_basis) (λ b hb, ⟨b, hb, bot_le⟩))

lemma coindep_nonempty (M : supermatroid α) : ∃ x, M.coindep x := ⟨⊥, M.bot_coindep⟩  

lemma coindep.coindep_of_le (hj : M.coindep j) (hij : i ≤ j) : M.coindep i :=
M.coindep_iff.mpr (exists.elim (M.coindep_iff.mp hj) (λ b hb', ⟨b, hb'.1, hij.trans hb'.2⟩))

lemma cobasis.coindep (hb : M.cobasis b) : M.coindep b := hb.1 

lemma cobasis.coindep_of_le (hb : M.cobasis b) (hib : i ≤ b) : M.coindep i := 
hb.coindep.coindep_of_le hib 

lemma cobasis.eq_of_le_coindep (hb : M.cobasis b) (hbi : b ≤ i) (hi : M.coindep i) : b = i := 
hb.2 hi hbi

lemma coindep_lower_set (M : supermatroid α) : 
is_lower_set M.coindep := λ i j hij hi, hi.coindep_of_le hij

lemma coindep_augment (M : supermatroid α) : 
  augmentable M.coindep := 
begin
  rintros i ⟨b, hb_b, hib⟩ j hic_nb hjc_b, 
  rw [←cobasis_iff, cobasis_iff_pcompl_basis] at hic_nb hjc_b,  
   
  obtain ⟨b'',hb''_b,hjb'',hb''ji⟩ := (hjc_b.indep.inf_left_indep iᵒ).le_basis_sup hb_b, 
  
  have hb''_lt_io : b'' < iᵒ, from 
  lt_of_le_of_ne 
    ((hb''ji.trans (sup_le_sup_left (le_pcompl_comm.mp hib) _)).trans (by simp))
    ( λ he, hic_nb ⟨(hic_nb (he.subst hb''_b)).elim, 
      λ a ha hia, by {subst he, exact hb''_b.eq_of_le_indep hia ha}⟩),
     
  refine ⟨b''ᵒ , ⟨lt_pcompl_comm.mp hb''_lt_io, _⟩,⟨b'',hb''_b, rfl.le⟩⟩,
  rwa [pcompl_le_comm, pcompl_sup], 
end 

lemma coindep_maximize (M : supermatroid α) : 
  maximizable M.coindep := 
begin
  rintros i₁ ⟨b,hb, hi₁b⟩ x hi₁x,
  obtain ⟨b₁,⟨hb₁x', hb₁, hb₁x⟩⟩:= hb.exists_extension_from xᵒ, 
  
  rw ←le_pcompl_comm at hi₁b, rw ←pcompl_le_iff at hi₁x,
  refine ⟨x ⊓ b₁ᵒ,
    ⟨⟨le_inf (pcompl_le_iff.mp hi₁x) (le_pcompl_comm.mp (hb₁x'.trans (sup_le hi₁x hi₁b))),
      inf_le_left⟩,
    M.coindep_iff.mpr ⟨b₁,hb₁,inf_le_right⟩⟩, λ a ha hxa, le_antisymm hxa (le_inf ha.1.2 _)⟩, 
  
  obtain ⟨⟨hi₁a, hax⟩, ⟨b₂,⟨hb₂,hab₂⟩⟩⟩ := ha, 

  rw le_pcompl_comm at ⊢ hab₂, 
  rw ←pcompl_le_iff at hax hxa hi₁a,
  rw [pcompl_inf, pcompl_pcompl] at hxa,  
  
  by_contradiction h, 
 
  have hi : ∃ i, b₁ ⊓ xᵒ ≤ i ⊓ xᵒ ∧ i < b₁ ∧ b₂ ⊔ xᵒ ≤ i ⊔ xᵒ :=
  begin
    refine ⟨b₁ ⊓ (xᵒ ⊔ b₂),
      le_inf (le_inf inf_le_left (inf_le_right.trans le_sup_left)) inf_le_right,
       lt_of_le_of_ne inf_le_left (λ h', h _),
       sup_le _ le_sup_right⟩,
    { rw ←h', exact inf_le_right.trans (sup_le hax hab₂),  },
    rw [inf_comm, inf_sup_assoc_of_le _ (le_sup_left : xᵒ ≤ xᵒ ⊔ b₂), @sup_comm _ _ xᵒ, le_inf_iff], 
    exact ⟨le_sup_left, by {rw sup_comm, exact hab₂.trans hxa}⟩,      
  end ,
 
  obtain ⟨i, hb₁i, hiltb₁, hxi⟩ := hi, 

  obtain ⟨b₃,hb₃, hib₃,hb₃i⟩ := 
    (hb₁.indep_of_le hiltb₁.le).lt_basis_sup (hb₁.not_basis_of_lt hiltb₁) hb₂, 

  have h₁ := @inf_lt_inf_of_lt_of_sup_le_sup _ _ _ _ _ xᵒ hib₃ 
    (sup_le (hb₃i.trans (sup_le le_sup_left (le_sup_left.trans hxi))) le_sup_right),  
  
  exact hb₁x.not_indep_of_lt (hb₁i.trans_lt h₁) inf_le_right (hb₃.inf_right_indep _),
end 

def dual (M : supermatroid α) : supermatroid α := 
{ indep := M.coindep,
  ind_nonempty := M.coindep_nonempty,
  ind_lower_set := M.coindep_lower_set,
  ind_augment := M.coindep_augment,
  ind_maximize := M.coindep_maximize }

lemma dual_ind_eq (M : supermatroid α)  : M.dual.indep = M.coindep := rfl 

lemma dual_indep_iff (M : supermatroid α) (i : α): M.dual.indep i ↔ M.coindep i := iff.rfl 

lemma dual_basis_iff (M : supermatroid α) (b : α) : M.dual.basis b ↔ M.cobasis b := iff.rfl 

lemma dual_bases_eq (M : supermatroid α) : M.dual.basis = M.cobasis := rfl 

@[simp] lemma dual_dual (M : supermatroid α) : M.dual.dual = M := 
bases_inj (by simp only [dual_bases_eq, cobases_eq_image_pcompl_bases, pcompl_pcompl_image])

end supermatroid 
