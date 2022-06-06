/-
Copyright (c) 2022 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Peter Nelson.
-/
import tactic 
import .prop_lemmas
import .lattice_intervals'
import order.lattice_intervals

/-!
# supermatroids 

In this file we define a `supermatroid`, namely a nonempty `lower_set` in a `semilattice_sup`
that satisfies certain augmentation axioms; its members are 'independent'. 

Lattice matroids do not appear in the literature, but ...
The definition and theory below is for supermatroids on an arbitrary type `E`, though most of the 
literature on supermatroids deals with the finite case. 

## Main content

- `indep`, `dep`, `coindep`, `basis`, `circuit`, `spanning` : predicates of the form `α → Prop`
  for various supermatroid properties on sets. Defining these as predicates enables dot notation, but
  most also have an alternative `set α` version which can work more smoothly with some parts
  of mathlib. 
- `supermatroid.dual` : the dual supermatroid of a supermatroid `M`; its bases are the complements of the bases
  of `M`. 
- `dual_dual`    : duality is idempotent. 

## References


TODO : rank, circuits, theory for finite supermatroids, etc etc. 
-/


universes u v
 
def supermatroid.extensible {α : Type u} [preorder α] (s : set α) : Prop := 
  ∀ (a ∈ s) b, a ≤ b → (maximals (≤) ((set.Icc a b) ∩ s)).nonempty

def supermatroid.augmentable {α : Type u} [semilattice_sup α] (s : set α) : Prop := 
  ∀ (a ∈ s) b, (a ∉ maximals (≤) s) → (b ∈ maximals (≤) s) → ((set.Ioc a (a ⊔ b)) ∩ s).nonempty 

open set 

@[ext] structure supermatroid (α : Type u) [semilattice_sup α] := 
(ind           : set α)
(ind_nonempty  : ind.nonempty ) 
(ind_lower_set : is_lower_set ind)
(ind_augment   : supermatroid.augmentable ind)
(ind_extension : supermatroid.extensible ind)

namespace supermatroid 

section basic 

variables {α : Type u} [distrib_lattice α] [bounded_order α] {M : supermatroid α} 
  {i j b x y c d r : α}

def indep (M : supermatroid α) : α → Prop := M.ind

def dep (M : supermatroid α) := λ x,¬ M.indep x 

def bases (M : supermatroid α) : set α := 
  maximals (≤) M.ind

def basis (M : supermatroid α) : α → Prop := M.bases

def basis_of (M : supermatroid α) : α → α → Prop := 
  λ b x, b ∈ maximals (≤) (λ Z, Z ≤ x ∧ M.indep Z)

def circuits (M : supermatroid α) : set α := 
  minimals (≤) M.indᶜ 

def circuit (M : supermatroid α) : α → Prop := M.circuits 

def spanning (M : supermatroid α) (x : α) := 
  ∃ b, b ≤ x ∧ M.basis b

@[simp] lemma mem_ind_iff : i ∈ M.ind ↔ M.indep i := iff.rfl   

@[simp] lemma mem_bases_iff : b ∈ M.bases ↔ M.basis b := iff.rfl 

lemma indep.indep_of_le (hi : M.indep i) (hJi : j ≤ i) : M.indep j := 
M.ind_lower_set hJi hi

lemma indep.inf_left_indep (hi : M.indep i) (x : α) : M.indep (x ⊓ i) := 
hi.indep_of_le inf_le_right

lemma indep.inf_right_indep (hi : M.indep i) (x : α) : M.indep (i ⊓ x) := 
hi.indep_of_le inf_le_left

lemma bot_indep (M : supermatroid α): M.indep ⊥ := 
exists.elim M.ind_nonempty (λ a (ha : M.indep a), ha.indep_of_le bot_le)

lemma indep.not_dep (hi : M.indep i) : ¬ M.dep i := 
  not_not_mem.mpr hi 

lemma dep.not_indep (hx : M.dep x) : ¬ M.indep x := 
  λ h, (h.not_dep hx).elim 

lemma not_dep_iff_indep : ¬ M.dep i ↔ M.indep i  := 
  ⟨λ h, by rwa [dep, not_not] at h, indep.not_dep⟩  

lemma indep_or_dep (i : α) : M.indep i ∨ M.dep i := 
  by {rw ←not_dep_iff_indep, apply em'}

lemma not_indep_iff_dep : ¬ M.indep i ↔ M.dep i := 
  by rw [←not_dep_iff_indep, not_not]

lemma dep.dep_of_lt (hx : M.dep x) (hxy : x ≤ y) : M.dep y := 
not_indep_iff_dep.mp (λ h, (hx.not_indep (h.indep_of_le hxy)).elim)

lemma indep.basis_of (hi : M.indep i) (hix : i ≤ x) (h : ∀ j, M.indep j → i ≤ j → j ≤ x → i = j) : 
  M.basis_of i x :=
⟨⟨hix,hi⟩, λ j h' h'', h j h'.2 h'' h'.1⟩ 

lemma indep.basis (hi : M.indep i) (hmax : ∀ j, M.indep j → i ≤ j → i = j) : M.basis i := 
⟨hi, λ j, hmax j⟩

lemma indep.extension (hi : M.indep i) (hix : i ≤ x) :
  ∃ j, i ≤ j ∧ M.basis_of j x := 
begin
  obtain ⟨j,⟨hj,(hj_ind : M.indep j)⟩,hj_max⟩ := M.ind_extension i hi x hix, 
  rw mem_Icc at hj, 
  refine ⟨j, hj.1, hj_ind.basis_of hj.2 (λ j' hj' hjj' hj'x, hj_max ⟨mem_Icc.mpr _,hj'⟩  hjj')⟩, 
  exact ⟨hj.1.trans hjj', hj'x⟩, 
end 

lemma basis.indep (h : M.basis b) : M.indep b := h.1 

lemma basis_of.indep (h : M.basis_of b x) : M.indep b := h.1.2 

lemma basis_of.le (h : M.basis_of b x) : b ≤ x := h.1.1 

lemma basis.inf_left_indep (hb : M.basis b) (x : α) : M.indep (x ⊓ b) := 
hb.indep.indep_of_le inf_le_right

lemma basis.inf_right_indep (hb : M.basis b) (x : α) : M.indep (b ⊓ x) := 
hb.indep.indep_of_le inf_le_left

lemma basis.eq_of_le_indep (h : M.basis b) (hbi : b ≤ i) (hi : M.indep i) : b = i := h.2 hi hbi

lemma basis.not_indep_of_lt (hb : M.basis b) (hbx : b < x) : ¬ M.indep x := 
λ hx,hbx.ne (hb.eq_of_le_indep hbx.le hx)

lemma basis_of.not_indep_of_lt (h : M.basis_of b x) (hby : b < y) (hYx : y ≤ x) : ¬ M.indep y := 
λ hi, (hby.ne ((h.2 (⟨hYx,hi⟩ : y ≤ x ∧ M.indep y) hby.le))).elim 

lemma basis_of.eq_of_le_indep (h : M.basis_of b x) (hby : b ≤ y) (hYx : y ≤ x) (hy : M.indep y): 
  b = y := 
by_contra (λ h', h.not_indep_of_lt (lt_of_le_of_ne hby h') hYx hy)

lemma basis_of.indep_of_le (hb : M.basis_of b x) (hib : i ≤ b)  : M.indep i := 
(hb.indep).indep_of_le hib 

lemma basis.basis_of_top (hb : M.basis b) : M.basis_of b ⊤ := 
hb.indep.basis_of le_top (λ j hj hbj _, (hb.eq_of_le_indep hbj hj)) 
    
lemma basis.indep_of_le (hb : M.basis b) (hib : i ≤ b) : M.indep i :=
hb.basis_of_top.indep_of_le hib

lemma basis.lt_not_basis (hb : M.basis b) (hbx : b < x) : ¬ M.basis x := 
λ hx, (hb.not_indep_of_lt hbx hx.indep)

lemma basis.not_basis_of_lt (hb : M.basis b) (hxb : x < b) : ¬ M.basis x := 
λ h, (h.lt_not_basis hxb) hb 

lemma basis_antichain (M : supermatroid α): is_antichain (≤) M.basis :=
λ x hx y hy hxy h, hy.not_basis_of_lt (lt_of_le_of_ne h hxy) hx

lemma circuit.not_indep (hc : M.circuit c) : ¬ M.indep c := hc.1 

lemma circuit.dep (hc : M.circuit c) : M.dep c := hc.1 

lemma circuit.indep_of_lt (hC : M.circuit c) (hiC : i < c) : M.indep i := 
  by_contra (λ h, (hiC.ne.symm) (hC.2 h hiC.le))

lemma exists_basis_of (M : supermatroid α) (x : α) : ∃ i, M.basis_of i x :=
exists.elim (M.bot_indep.extension (@bot_le _ _ _ x)) (λ a ha, ⟨a, ha.2⟩)

lemma indep.augment (hi : M.indep i) (hi_nb : ¬M.basis i) (hj : M.basis j) : 
  ∃ i', i < i' ∧ i' ≤ i ⊔ j ∧ M.indep i' := 
begin
  obtain ⟨i',⟨hi'_int, hi'_ind⟩⟩ := M.ind_augment _ hi _ hi_nb hj, 
  exact ⟨i', (mem_Ioc.mpr hi'_int).1, (mem_Ioc.mpr hi'_int).2, hi'_ind⟩, 
end 
  
lemma basis_of.basis (hb : M.basis_of b x) (hx : M.spanning x) : M.basis b := 
 by_contra (λ h, 
   ((exists.elim hx (λ b' hb', exists.elim (hb.indep.augment h (hb'.2))
   (λ j hj, hb.not_indep_of_lt hj.1 (hj.2.1.trans (sup_le hb.le hb'.1)) hj.2.2 )))))

lemma indep.extend_to_sup_basis {i b : α} (hi: M.indep i) (hb : M.basis b) : 
   ∃ b', M.basis b' ∧ i ≤ b' ∧ b' ≤ i ⊔ b :=
exists.elim (hi.extension (@le_sup_left _ _ i b)) 
  (λ b' h, ⟨b',⟨h.2.basis ⟨b, le_sup_right, hb⟩,h.1,h.2.1.1⟩⟩)

lemma exists_basis (M : supermatroid α): ∃ b, M.basis b := 
begin
  obtain ⟨b, ⟨-,hb⟩⟩ := M.bot_indep.extension (@bot_le α _ _ ⊤), 
  exact ⟨b, hb.indep.basis (λ j hj hbj, hb.eq_of_le_indep hbj le_top hj)⟩, 
end 

lemma top_spanning (M : supermatroid α) : M.spanning ⊤ := 
exists.elim (M.exists_basis) (λ b hb, ⟨b,le_top,hb⟩)

lemma indep.extends_to_basis (hi : M.indep i) : 
  ∃ b, i ≤ b ∧ M.basis b := 
exists.elim (hi.extension (@le_top _ _ _ i))
  (λ b hb, ⟨b, hb.1, hb.2.indep.basis (λ j hj hbj, hb.2.eq_of_le_indep hbj le_top hj)⟩)

lemma indep_iff_le_basis : 
  M.indep i ↔ ∃ b, i ≤ b ∧ M.basis b := 
⟨indep.extends_to_basis, λ h, exists.elim h (λ b hi, hi.2.indep_of_le hi.1)⟩

lemma bases_inj {M₁ M₂ : supermatroid α} (hb : M₁.bases = M₂.bases)  : M₁ = M₂ := 
  by {ext, simp_rw [mem_ind_iff, indep_iff_le_basis, ←mem_bases_iff, hb]}

end basic 

section dual 

variables {α : Type u} [boolean_algebra α] {M : supermatroid α} {i j b x y c d r : α}

def coindep (M : supermatroid α) : α → Prop := 
  λ i, ∃ (b : α), (M.basis b ∧ i ≤ bᶜ)

def coind (M : supermatroid α) : set α := M.coindep 

def cobases (M : supermatroid α) : set α := maximals (≤) M.coind

def cobasis (M : supermatroid α) : α → Prop := M.cobases

@[simp] lemma mem_coind_iff : i ∈ M.coind ↔ M.coindep i := iff.rfl 

@[simp] lemma mem_cobases_iff : b ∈ M.cobases ↔ M.cobasis b := iff.rfl 

lemma indep.diff_indep (hi : M.indep i) (x : α) : M.indep (i \ x) := 
hi.indep_of_le (sdiff_le)

lemma basis.diff_indep (hb : M.basis b) (x : α) : M.indep (b \ x) := 
hb.indep_of_le (sdiff_le)

lemma cobases_eq_image_compl_bases (M : supermatroid α) : 
  M.cobases = compl '' M.bases := 
by {convert (M.basis_antichain.img_compl.max_lower_set_of), simpa [cobases]}

lemma coindep_iff (M : supermatroid α) : 
   M.coindep x ↔ ∃ b, (M.basis b ∧ x ≤ bᶜ) := iff.rfl 

lemma coindep.exists_disj_basis (hi : M.coindep i): ∃ b, M.basis b ∧ disjoint i b := 
  exists.elim hi (λ b hb, ⟨b, hb.1, disjoint_iff_le_compl_right.mpr hb.2⟩)

lemma cobasis_iff_compl_basis (M : supermatroid α) :
  M.cobasis b ↔ M.basis bᶜ :=
by {rw [←mem_bases_iff, ←mem_cobases_iff, cobases_eq_image_compl_bases ,mem_compl_image']}

lemma bot_coindep (M : supermatroid α) : M.coindep ⊥ := 
M.coindep_iff.mpr (exists.elim (M.exists_basis) (λ b hb, ⟨b, hb, bot_le⟩))

lemma coindep_nonempty (M : supermatroid α) : M.coind.nonempty := ⟨⊥, M.bot_coindep⟩  

lemma coindep.coindep_of_le (hj : M.coindep j) (hij : i ≤ j) : M.coindep i :=
M.coindep_iff.mpr (exists.elim (M.coindep_iff.mp hj) (λ b hb', ⟨b, hb'.1, hij.trans hb'.2⟩))

lemma coindep_lower_set (M : supermatroid α) : 
is_lower_set M.coind  := λ i j hij hi, hi.coindep_of_le hij

lemma coind_augment (M : supermatroid α) : 
  augmentable M.coind := 
begin
  intros i hi j hic_nb hjc_b, 
  rw [←cobases, mem_cobases_iff, cobasis_iff_compl_basis] at hic_nb hjc_b,  
  
  obtain ⟨b, hb_b, hb_disj⟩ := hi.exists_disj_basis, 
  obtain ⟨b'',hb''_b,hjb'',hb''ji⟩ := (hjc_b.diff_indep i).extend_to_sup_basis hb_b, 
  
  have hib'' : i < b''ᶜ := 
    lt_of_le_of_ne 
      (disjoint_iff_le_compl_right.mp 
        (disjoint.mono_right hb''ji (disjoint_sup_right.mpr ⟨disjoint_sdiff_self_right, hb_disj⟩))) 
      (λ he, hic_nb _), 
  
  swap, {subst he, convert hb''_b, simp},
  refine ⟨b''ᶜ, mem_Ioc.mpr ⟨hib'',_⟩, M.coindep_iff.mpr ⟨b'', hb''_b, rfl.le⟩⟩,
  rwa [sdiff_eq, ←compl_sup, compl_le_iff_compl_le, sup_comm] at hjb'', 
end 

lemma coind_extension (M : supermatroid α) : 
  extensible M.coindep := 
begin
  rintros i₁ ⟨b,hb_b, hi₁b⟩ x hi₁x,  
  obtain ⟨i,hi⟩ := M.exists_basis_of xᶜ, 
  obtain ⟨b', ⟨hb'b, hib', hb'i⟩⟩ := hi.indep.extend_to_sup_basis hb_b,   
  
  refine ⟨x ⊓ b'ᶜ, 
    ⟨mem_Icc.mp ⟨le_inf hi₁x _, inf_le_left⟩, M.coindep_iff.mpr ⟨b', hb'b, inf_le_right⟩⟩, _⟩, 
  { rw ←disjoint_iff_le_compl_right at hi₁b ⊢, 
    exact disjoint.mono_right hb'i 
      (disjoint_sup_right.mpr ⟨disjoint.mono hi₁x hi.le disjoint_compl_right,hi₁b⟩)},
  
  rintros y ⟨hy_int,(hy_i : M.coindep y)⟩ hxy, 
  obtain ⟨b'',⟨hb''b, hYb''⟩⟩ := hy_i.exists_disj_basis, 
  obtain ⟨hi₁y, hyx⟩ := mem_Icc.mp hy_int, 
  suffices h2Yb': disjoint y b', 
    from hxy.antisymm (le_inf hyx (disjoint_iff_le_compl_right.mp h2Yb')),
  
  have hb''x : b'' ⊓ x ≤ b' ⊓ x, 
  begin
    refine le_inf_iff.mpr ⟨_,inf_le_right⟩, 
    rw [←sup_inf_sdiff x b', sdiff_eq, inf_sup_left, sup_le_iff, ←inf_assoc],
    refine ⟨inf_le_right, 
    (inf_le_inf_left b'' (hxy.trans (disjoint_iff_le_compl_right.mp hYb''))).trans _⟩, 
    rw [inf_compl_eq_bot], 
    exact bot_le, 
  end, 

  have hi'b : ((b'' ⊓ x) ⊔ (b' ⊓ xᶜ)) ≤ b' := 
    sup_le (hb''x.trans (inf_le_left)) inf_le_left,  

  by_cases h1i' : ((b'' ⊓ x) ⊔ (b' ⊓ xᶜ)) = b', 
  { rw [←h1i', disjoint_sup_right],  
    exact ⟨disjoint.inf_right _ hYb'', 
      disjoint.mono_left hyx (disjoint.mono_right inf_le_right disjoint_compl_right)⟩},
  
  obtain ⟨i'',⟨hi'i'', hi''b'', hi''i⟩⟩ :=  (hb'b.indep_of_le hi'b).augment
    (hb'b.not_basis_of_lt (lt_of_le_of_ne hi'b h1i')) hb''b ,
    
  have hii' : i ≤ (b'' ⊓ x ⊔ b' ⊓ xᶜ) ⊓ xᶜ := 
    le_inf (le_sup_of_le_right (le_inf hib' hi.le)) hi.le, 

  have hi'i'' : (b'' ⊓ x ⊔ b' ⊓ xᶜ) ⊓ xᶜ < i'' ⊓ xᶜ := 
  begin 
    simp only [inf_sup_right, inf_assoc, inf_compl_eq_bot, inf_bot_eq, inf_idem, bot_sup_eq], 
    refine lt_of_le_of_ne (le_trans (by simp) (inf_le_inf_right xᶜ hi'i''.le)) (λ h_eq, _), 
    rw [←sup_inf_sdiff i'' x, sdiff_eq, ←h_eq] at hi'i'', 
    rw [sup_right_comm, ←@sup_comm _ _ b'', sup_inf_self] at hi''b'',
    have h_last := lt_of_lt_of_le hi'i'' (sup_le_sup_right (inf_le_inf_right x hi''b'') _), 
    simp [inf_sup_right, inf_assoc] at h_last, assumption
  end,
  
  have hi'i'' := lt_of_le_of_lt hii' hi'i'', 
  exact (hi'i''.ne (hi.2 (⟨inf_le_right, hi''i.indep_of_le (inf_le_left) ⟩) hi'i''.le)).elim, 
end 

def dual (M : supermatroid α) : supermatroid α := 
{ ind := M.coind,
  ind_nonempty := M.coindep_nonempty,
  ind_lower_set := M.coindep_lower_set,
  ind_augment := M.coind_augment,
  ind_extension := M.coind_extension }

lemma dual_ind_eq (M : supermatroid α)  : M.dual.ind = M.coind := rfl 

lemma dual_indep_iff (M : supermatroid α) (i : α): M.dual.indep i ↔ M.coindep i := iff.rfl 

lemma dual_basis_iff (M : supermatroid α) (b : α) : M.dual.basis b ↔ M.cobasis b := iff.rfl 

lemma dual_bases_eq (M : supermatroid α) : M.dual.bases = M.cobases := rfl 

@[simp] lemma dual_dual (M : supermatroid α) : M.dual.dual = M := 
bases_inj (by simp only [dual_bases_eq, cobases_eq_image_compl_bases, compl_compl_image'])

end dual 


section iso 

variables {α : Type u} {β : Type v} [semilattice_sup α] [semilattice_sup β] {M : supermatroid α} 
  {N : supermatroid β}

structure supermatroid_iso (M : supermatroid α) (M' : supermatroid β) : Type (max u v) :=
(to_equiv  : α ≃o β)
(on_ind : ∀ a, M.ind a ↔ M'.ind (to_equiv a) )

infix `≃l` :25 := supermatroid_iso 




end iso 

section minor



variables {α : Type u} [distrib_lattice α] [bounded_order α] {M : supermatroid α} {c d r : α}

--def contract {M : supermatroid α} (c : α) (hc : M.indep c) : sorry



-- #check supermatroid.circuit M


end minor 

end supermatroid 