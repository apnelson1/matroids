/-
Copyright (c) 2022 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Peter Nelson.
-/
import tactic 
import .prop_lemmas

/-!
# Matroids 

In this file we define a `matroid`, namely a subset of the power set of a ground type `E` that is
down-closed, and satisfies certain augmentation axioms; its members are 'independent sets'. 

The definition and theory below is for matroids on an arbitrary type `E`, though most of the 
literature on matroids deals with the finite case. 

## Main content

- `indep`, `dep`, `coindep`, `basis`, `circuit`, `spanning` : predicates of the form `set E → Prop`
  for various matroid properties on sets. Defining these as predicates enables dot notation, but
  most also have an alternative `set (set E)` version which can work more smoothly with some parts
  of mathlib. 
- `matroid.dual` : the dual matroid of a matroid `M`; its bases are the complements of the bases
  of `M`. 
- `dual_dual`    : duality is idempotent. 

## References

See [Oxley] for a general reference of matroids, and [Diestel,et,al] for the specific axiomatization
developed here. 

TODO : rank, circuits, theory for finite matroids, etc etc. 
-/


universes u v
 
def extensible' {α : Type u} [preorder α] (s : set α) : Prop := 
  ∀ (a ∈ s) b, a ≤ b → (maximals (≤) ((set.Icc a b) ∩ s)).nonempty 

def augmentable' {α : Type u} [lattice α] (s : set α) : Prop := 
  ∀ (a ∈ s) b, (a ∉ maximals (≤) s) → (b ∈ maximals (≤) s) → ((set.Ioc a (a ⊔ b)) ∩ s).nonempty 

open set 

variables {E : Type u}


def extensible {α : Type u} (s : set (set α)) : Prop := 
  ∀ a x, a ∈ s → a ⊆ x → (maximals (⊆) (λ y, a ⊆ y ∧ y ⊆ x ∧ y ∈ s)).nonempty 

-- lemma extensible_iff_extensible' (s : set (set E)) : extensible s ↔ extensible' s := 
-- begin
--   refine ⟨λ h, λ a has b hab, exists.elim ⟨_,_⟩, λ h, λ a x has hax, _⟩, 
--end 

def augmentable {α : Type u} (s : set (set α)) : Prop := 
  ∀ (a b : set α), a ∈ s → ¬(a ∈ maximals (⊆) s) → (b ∈ maximals (⊆) s) → 
    (∃ x, x ∉ a ∧ x ∈ b ∧ (a.insert x) ∈ s)

@[ext] structure matroid (E : Type u):= 
(indep_sets           : set (set E))
(empty_mem_indep_sets : ∅ ∈ indep_sets) 
(indep_sets_lower_set : is_lower_set indep_sets)
(indep_sets_augment   : augmentable indep_sets)
(indep_sets_extension : extensible indep_sets)

namespace matroid 

variables {M : matroid E} {I J B X Y C : set E}

section basic 

def indep (M : matroid E) := M.indep_sets 

def dep (M : matroid E) := λ X, ¬ M.indep X 

def bases (M : matroid E) : set (set E) := 
  maximals (⊆) M.indep_sets

def basis (M : matroid E) : set E → Prop := M.bases

def basis_of (M : matroid E) : set E → set E → Prop := 
  λ B X, B ∈ maximals (⊆) (λ Z, Z ⊆ X ∧ M.indep Z)

def circuits (M : matroid E) : set (set E) := 
  minimals (⊆) M.indep_setsᶜ 

def circuit (M : matroid E) : set E → Prop := M.circuits 

def spanning (M : matroid E) (X : set E) := 
  ∃ B, B ⊆ X ∧ M.basis B

def coindep (M : matroid E) : set E → Prop := 
  λ I, ∃ B, (M.basis B ∧ I ⊆ Bᶜ)

def coindep_sets (M : matroid E) : set (set E) := M.coindep 

def cobases (M : matroid E) : set (set E) := maximals (⊆) M.coindep_sets

def cobasis (M : matroid E) : set E → Prop := M.cobases  

@[simp] lemma mem_indep_sets_iff : I ∈ M.indep_sets ↔ M.indep I := iff.rfl 

@[simp] lemma mem_coindep_sets_iff : I ∈ M.coindep_sets ↔ M.coindep I := iff.rfl 

@[simp] lemma mem_bases_iff : B ∈ M.bases ↔ M.basis B := iff.rfl 

@[simp] lemma mem_cobases_iff : B ∈ M.cobases ↔ M.cobasis B := iff.rfl 

lemma empty_indep (M : matroid E): M.indep ∅ := M.empty_mem_indep_sets 

lemma indep.not_dep (hI : M.indep I) : ¬ M.dep I := 
  not_not_mem.mpr hI 

lemma dep.not_indep (hX : M.dep X) : ¬ M.indep X := 
  λ h, (h.not_dep hX).elim 

lemma not_dep_iff_indep : ¬ M.dep I ↔ M.indep I  := 
  ⟨λ h, by rwa [dep, not_not] at h, indep.not_dep⟩  

lemma indep_or_dep (I : set E) : M.indep I ∨ M.dep I := 
  by {rw ←not_dep_iff_indep, apply em'}

lemma not_indep_iff_dep : ¬ M.indep I ↔ M.dep I := 
  by rw [←not_dep_iff_indep, not_not]

lemma indep.subset (hI : M.indep I) (hJI : J ⊆ I) : M.indep J := 
M.indep_sets_lower_set hJI hI

lemma dep.supset (hX : M.dep X) (hXY : X ⊆ Y) : M.dep Y := 
not_indep_iff_dep.mp (λ h, (hX.not_indep (h.subset hXY)).elim)

lemma indep.extension (hI : M.indep I) (hIX : I ⊆ X) :
  ∃ J, I ⊆ J ∧ M.basis_of J X := 
exists.elim (M.indep_sets_extension I X hI hIX) 
  (λ J hJ, ⟨J, hJ.1.1, ⟨hJ.1.2, λ Z hZ hJZ, hJ.2 ( ⟨hJ.1.1.trans hJZ, hZ⟩) hJZ⟩⟩) 

lemma indep.augment (hI : M.indep I) (hI_nb : ¬ M.basis I) (hJ : M.basis J): 
  ∃ x, x ∉ I ∧ x ∈ J ∧ M.indep (I.insert x) := 
M.indep_sets_augment _ _ hI hI_nb hJ 

lemma indep.basis_of (hI : M.indep I) (hIX : I ⊆ X) (h : ∀ J, M.indep J → I ⊆ J → J ⊆ X → I = J) : 
  M.basis_of I X :=
⟨⟨hIX,hI⟩, λ J h' h'', h J h'.2 h'' h'.1⟩ 

lemma indep.basis (hI : M.indep I) (hmax : ∀ J, M.indep J → I ⊆ J → I = J) : M.basis I := 
⟨hI, λ J, hmax J⟩

lemma basis.indep (h : M.basis B) : M.indep B := h.1 

lemma basis_of.indep (h : M.basis_of B X) : M.indep B := h.1.2 

lemma basis_of.subset (h : M.basis_of B X) : B ⊆ X := h.1.1 

lemma basis.eq_of_supset_indep (h : M.basis B) (hBI : B ⊆ I) (hI : M.indep I) : B = I :=
h.2 hI hBI

lemma basis.not_indep_of_ssupset (hB : M.basis B) (hBX : B ⊂ X) : ¬ M.indep X := 
λ hX, hBX.ne (hB.eq_of_supset_indep hBX.subset hX)

lemma basis_of.ssupset_not_indep (h : M.basis_of B X) (hBY : B ⊂ Y) (hYX : Y ⊆ X) : ¬ M.indep Y := 
λ hI, (hBY.ne ((h.2 (⟨hYX, hI⟩ : Y ⊆ X ∧ M.indep Y) hBY.1))).elim 

lemma basis_of.eq_of_supset_indep (h : M.basis_of B X) (hBY : B ⊆ Y) (hYX : Y ⊆ X) (hY : M.indep Y): 
  B = Y := 
by_contra (λ h', h.ssupset_not_indep (ssubset_of_ne_of_subset h' hBY) hYX hY)

lemma basis_of.subset_indep (hB : M.basis_of B X) (hIB : I ⊆ B)  : M.indep I := 
(hB.indep).subset hIB 

lemma basis.basis_of_univ (hB : M.basis B) : M.basis_of B univ := 
hB.indep.basis_of B.subset_univ (λ J hJ hBJ _, (hB.eq_of_supset_indep hBJ hJ)) 
    
lemma basis.subset_indep (hB : M.basis B) (hIB : I ⊆ B) : M.indep I:=
hB.basis_of_univ.subset_indep hIB

lemma basis.not_basis_of_ssupset (hB : M.basis B) (hBX : B ⊂ X) : ¬ M.basis X := 
λ h, (hB.not_indep_of_ssupset hBX) h.1  

lemma basis.not_basis_of_ssubset (hB : M.basis B) (hXB : X ⊂ B) : ¬ M.basis X := 
λ h, (h.not_basis_of_ssupset hXB) hB 

lemma basis_antichain (M : matroid E): is_antichain (⊆) M.basis :=
λ X hX Y hY hXY h, hY.not_basis_of_ssubset (ssubset_of_ne_of_subset hXY h) hX

lemma circuit.dep (hC : M.circuit C) : ¬ M.indep C := hC.1 

lemma circuit.indep_of_ssubset (hC : M.circuit C) (hIC : I ⊂ C) : M.indep I := 
  by_contra (λ h, (hIC.ne.symm) (hC.2 h hIC.subset))

lemma exists_basis_of (M : matroid E) (X : set E) : 
  ∃ I, M.basis_of I X :=
exists_imp_exists (λ a (ha : ∅ ⊆ a ∧ M.basis_of a X), ha.2) 
  (M.empty_indep.extension (empty_subset X)) 

lemma indep.augment_set (hI : M.indep I) (hI_nb : ¬M.basis I) (hJ : M.basis J) : 
  ∃ I', I ⊂ I' ∧ I' ⊆ I ∪ J ∧ M.indep I' := 
exists.elim (hI.augment hI_nb hJ) 
  (λ x hx, ⟨I.insert x, ssubset_insert hx.1, insert_subset.mpr 
    ⟨mem_union_right _ hx.2.1,subset_union_left _ _⟩,hx.2.2⟩)
  
lemma basis_of.basis (hB : M.basis_of B X) (hX : M.spanning X) : M.basis B := 
by_contra (λ h, 
  ((exists.elim hX (λ B' hB', exists.elim (hB.1.2.augment_set h (hB'.2))
  (λ J hJ, hB.ssupset_not_indep hJ.1 (hJ.2.1.trans (union_subset hB.subset hB'.1)) hJ.2.2 )))))

lemma indep.extend_to_union_basis {I B : set E} (hI: M.indep I) (hB : M.basis B) : 
   ∃ B', M.basis B' ∧ I ⊆ B' ∧ B' ⊆ I ∪ B :=
exists.elim 
  (hI.extension (I.subset_union_left B))
  (λ B' h, ⟨B',⟨h.2.basis ⟨B, I.subset_union_right _, hB⟩,h.1,h.2.1.1⟩⟩)

lemma exists_basis (M : matroid E): ∃ B, M.basis B := 
exists.elim (M.empty_indep.extension ((∅ : set E).subset_univ)) 
  (λ B hB, ⟨B, hB.2.indep, λ B' hB' hBB', hB.2.eq_of_supset_indep hBB' B'.subset_univ hB'⟩)

lemma univ_spanning (M : matroid E) : M.spanning univ := 
exists.elim (M.exists_basis) (λ B hB, ⟨B,B.subset_univ,hB⟩)

lemma indep.extends_to_basis (hI : M.indep I) : 
  ∃ B, I ⊆ B ∧ M.basis B := 
exists.elim (hI.extension I.subset_univ)
  (λ B hB, ⟨B, hB.1, hB.2.indep.basis (λ J hJ hBJ, hB.2.eq_of_supset_indep hBJ J.subset_univ hJ)⟩)

lemma indep_iff_subset_basis : 
  M.indep I ↔ ∃ B, I ⊆ B ∧ M.basis B := 
⟨indep.extends_to_basis, λ h, exists.elim h (λ B hI, hI.2.subset_indep hI.1)⟩

lemma bases_inj {M₁ M₂ : matroid E} (hB : M₁.bases = M₂.bases)  : M₁ = M₂ := 
  by {ext, simp_rw [mem_indep_sets_iff, indep_iff_subset_basis, ←mem_bases_iff, hB]}

end basic 

section dual 

lemma cobases_eq_image_compl_bases (M : matroid E) : 
  M.cobases = compl '' M.bases := 
by {convert (M.basis_antichain.img_compl.max_lower_set_of), simpa [cobases]}

lemma coindep_iff (M : matroid E) : 
   M.coindep X ↔ ∃ B, (M.basis B ∧ X ⊆ Bᶜ) := iff.rfl 

lemma coindep.exists_disj_basis (hI : M.coindep I): ∃ B, M.basis B ∧ disjoint I B := 
  exists.elim hI (λ B hB, ⟨B, hB.1, disjoint_iff_subset_compl_right.mpr hB.2⟩)

lemma cobasis_iff_compl_basis (M : matroid E) :
  M.cobasis B ↔ M.basis Bᶜ :=
by rw [←mem_bases_iff, ←mem_cobases_iff, cobases_eq_image_compl_bases, mem_compl_image]

lemma empty_coindep (M : matroid E) : M.coindep ∅ := 
M.coindep_iff.mpr (exists.elim (M.exists_basis) (λ B hB, ⟨B, hB, Bᶜ.empty_subset⟩))
  
lemma coindep.subset (hJ : M.coindep J) (hIJ : I ⊆ J) : M.coindep I :=
M.coindep_iff.mpr (exists.elim (M.coindep_iff.mp hJ) (λ B hB', ⟨B, hB'.1, hIJ.trans hB'.2⟩))

lemma coindep_lower_set (M : matroid E) : 
is_lower_set M.coindep_sets  := λ I J hIJ hI, @coindep.subset _ _ _ _ hI hIJ

lemma coindep_sets_augment (M : matroid E) : 
  augmentable M.coindep_sets := 
begin
  intros I J hI hIc_nb hJc_b, 
  rw [←cobases, mem_cobases_iff, cobasis_iff_compl_basis] at hIc_nb hJc_b,  
  
  obtain ⟨B, hB_b, hB_disj⟩ := hI.exists_disj_basis, 
  obtain ⟨B'',hB''_b,hJB'',hb''JI⟩ := 
    (hJc_b.subset_indep (diff_subset Jᶜ I)).extend_to_union_basis hB_b, 
  
  have hIB''1 : disjoint I B'' := by { 
    refine disjoint_of_subset_right hb''JI _, 
    rw [diff_eq, disjoint_union_right],
    exact ⟨disjoint.inter_right' _ disjoint_compl_right, hB_disj⟩},
  
  have hIB'' : I ⊂ B''ᶜ := 
    ssubset_of_ne_of_subset (λ h_eq, hIc_nb _) (disjoint_iff_subset_compl_right.mp hIB''1), 

  swap, {subst h_eq, convert hB''_b, simp},
  
  obtain ⟨x, hxI, hx⟩ := ssubset_iff_insert.mp hIB'', 
  refine ⟨x, hxI, by_contra (λ hxJ, _), ⟨B'', hB''_b, hx⟩⟩ ,
  
  exact mem_of_mem_of_subset 
    (mem_insert x I) hx 
    (mem_of_mem_of_subset (mem_inter (mem_compl hxJ) (mem_compl hxI)) hJB''), 
end 

lemma coindep_sets_extension (M : matroid E) : 
  extensible M.coindep := 
begin
  rintros I₁ X ⟨B, hBb, hI₁B⟩ hI₁J,   
  obtain ⟨I, hI⟩ := M.exists_basis_of Xᶜ,
  obtain ⟨B', ⟨hB'b, hIB', hB'I⟩⟩ := hI.indep.extend_to_union_basis hBb,   
  
  refine ⟨X ∩ B'ᶜ, ⟨subset_inter hI₁J _ , 
    inter_subset_left _ _, M.coindep_iff.mpr ⟨B', hB'b, inter_subset_right _ _⟩⟩, _⟩,  
  { rw ←disjoint_iff_subset_compl_right at hI₁B ⊢,
    refine disjoint_of_subset_right hB'I (disjoint_union_right.mpr ⟨_,hI₁B⟩),
    exact disjoint_of_subset hI₁J hI.subset disjoint_compl_right},
  
  rintros Y ⟨hI₁Y, hYX, hYi⟩ hXY, 
  obtain ⟨B'',⟨hB''b, hYB''⟩⟩ := hYi.exists_disj_basis, 

  suffices h2YB': disjoint Y B', 
    from hXY.antisymm (subset_inter hYX (disjoint_iff_subset_compl_right.mp h2YB')),
  
  have hB''X : B'' ∩ X ⊆ B' ∩ X := λ x hx, 
  by {rw mem_inter_iff at ⊢ hx, 
    exact ⟨by_contra (λ hxB', hYB''.mem_inter_elim 
      (mem_inter (hXY (mem_inter hx.2 (mem_compl hxB'))) hx.1)), hx.2⟩},
  
  have hI'B : ((B'' ∩ X) ∪ (B' ∩ Xᶜ)) ⊆ B'  := 
    union_subset (hB''X.trans (inter_subset_left _ _)) (diff_subset _ _),  

  by_cases h1I' : ((B'' ∩ X) ∪ (B' ∩ Xᶜ)) = B', 
  { rw ←h1I', 
    exact disjoint_union_right.mpr 
      ⟨disjoint.inter_right _ hYB'', disjoint_of_subset_left hYX (disjoint_diff)⟩},

  obtain ⟨I'',⟨hI'I'', hI''B'', hI''i⟩⟩ :=  (hB'b.subset_indep hI'B).augment_set 
    (hB'b.not_basis_of_ssubset (ssubset_of_ne_of_subset h1I' hI'B)) hB''b ,
    
  obtain ⟨x, ⟨h1x, h2x⟩⟩ := exists_of_ssubset hI'I'', 
  
  have hx' := mem_of_mem_of_subset h1x hI''B'', 
  have hx : x ∈ I'' ∧ x ∈ Xᶜ ∧ x ∉ B' := by finish,
  -- finish is slow. Need a set solver tactic! 
  
  have hII' : I ⊆ (B'' ∩ X ∪ B' ∩ Xᶜ) ∩ Xᶜ, from
    subset_inter (subset_union_of_subset_right (subset_inter hIB' hI.subset) _) hI.subset, 

  have hI'I'' : (B'' ∩ X ∪ B' ∩ Xᶜ) ∩ Xᶜ ⊂ I'' ∩ Xᶜ, 
  by {
    simp only [inter_distrib_right, inter_assoc, inter_compl_self, inter_empty, inter_self, 
      empty_union], 
    refine (ssubset_iff_of_subset (subset_inter _ _)).mpr 
      ⟨x, ⟨mem_inter hx.1 hx.2.1, (λ h, hx.2.2 h.1)⟩⟩, 
    { exact subset.trans (subset_union_right _ _) hI'I''.subset},
    exact inter_subset_right _ _}, 

  have hI'I'' := ssubset_of_subset_of_ssubset hII' hI'I'', 
  
  exact (hI'I''.ne (hI.2 (⟨inter_subset_right _ _, 
    hI''i.subset (inter_subset_left _ _) ⟩) hI'I''.subset)).elim, 
end 

def dual (M : matroid E) : matroid E := 
{ indep_sets := M.coindep_sets,
  empty_mem_indep_sets := M.empty_coindep,
  indep_sets_lower_set := M.coindep_lower_set,
  indep_sets_augment := M.coindep_sets_augment,
  indep_sets_extension := M.coindep_sets_extension }

lemma dual_indep_sets_eq (M : matroid E)  : M.dual.indep_sets = M.coindep_sets := rfl 

lemma dual_indep_iff (M : matroid E) (I : set E): M.dual.indep I ↔ M.coindep I := iff.rfl 

lemma dual_basis_iff (M : matroid E) (B : set E) : M.dual.basis B ↔ M.cobasis B := iff.rfl 

lemma dual_bases_eq (M : matroid E) : M.dual.bases = M.cobases := rfl 

@[simp] lemma dual_dual (M : matroid E) : M.dual.dual = M := 
bases_inj (by simp only [dual_bases_eq, cobases_eq_image_compl_bases, compl_compl_image])

end dual 

end matroid 