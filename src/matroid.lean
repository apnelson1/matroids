/-
Copyright (c) 2022 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Peter Nelson.
-/
import .supermatroid 
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
 
variables {E : Type u}

def matroid (E : Type u) := supermatroid (set E)

open set 

namespace matroid 

variables {M : matroid E} {I J B X Y C : set E}

section basic 

def indep (M : matroid E) : (set E → Prop) := M.indep  
def indep_sets (M : matroid E) : set (set E) := M.indep 
def basis (M : matroid E) : (set E → Prop) := M.basis 
def bases (M : matroid E) : (set (set E)) := M.basis 
def coindep (M : matroid E) : (set E → Prop) := M.coindep
def coindep_sets (M : matroid E) : (set (set E)) := M.coindep
def spanning (M : matroid E) : (set E → Prop) := M.spanning
def circuit (M : matroid E) : (set E → Prop) := M.circuit 
def circuits (M : matroid E) : (set (set E)) := M.circuit

@[simp] lemma mem_indep_sets_iff : I ∈ M.ind ↔ M.indep I := iff.rfl 

@[simp] lemma mem_coindep_sets_iff : I ∈ M.coind ↔ M.coindep I := iff.rfl 

@[simp] lemma mem_bases_iff : B ∈ M.bases ↔ M.basis B := iff.rfl 

@[simp] lemma mem_cobases_iff : B ∈ M.cobases ↔ M.cobasis B := iff.rfl 

lemma empty_indep (M : matroid E): M.indep ∅ := M.bot_indep 

lemma indep.indep_of_subset (hI : M.indep I) (hJI : J ⊆ I) : M.indep J := hI.indep_of_le hJI

lemma indep.inter_left_indep (hI : M.indep I) (X : set E) : M.indep (X ∩ I) := hI.inf_left_indep X

lemma indep.inter_right_indep (hI : M.indep I) (X : set E) : M.indep (I ∩ X) := hI.inf_right_indep X

lemma indep.diff_indep (hI : M.indep I) (X : set E) : M.indep (I \ X) := hI.inter_right_indep _  

lemma dep.dep_of_supset (hX : M.dep X) (hXY : X ⊆ Y) : M.dep Y := hX.dep_of_lt hXY 

lemma indep.extension (hI : M.indep I) (hIX : I ⊆ X) : ∃ J, I ⊆ J ∧ M.basis_of J X := 
hI.extension hIX 

lemma indep.augment (hI : M.indep I) (hI_nb : ¬M.basis I) (hJ : M.basis J) : 
  ∃ I', I ⊂ I' ∧ I' ⊆ I ∪ J ∧ M.indep I' := 
hI.augment hI_nb hJ 

lemma indep.augment_insert (hI : M.indep I) (hI_nb : ¬ M.basis I) (hJ : M.basis J): 
  ∃ x, x ∉ I ∧ x ∈ J ∧ M.indep (I.insert x) := 
begin 
  obtain ⟨I', hII', hI'IJ, hI'⟩ := hI.augment hI_nb hJ, 
  obtain ⟨x, hxI, hx⟩ :=  ssubset_iff_insert.mp hII', 
  refine ⟨x, hxI, _, hI'.indep_of_subset hx⟩, 
  
  have h := mem_of_mem_of_subset 
    ((mem_diff x).mpr ⟨(mem_insert x I), hxI⟩) 
    (diff_subset_diff_left (hx.trans hI'IJ)), 
  simp only [union_diff_left, mem_diff] at h, 
  exact h.1,
end 

lemma indep.basis_of (hI : M.indep I) (hIX : I ⊆ X) (h : ∀ J, M.indep J → I ⊆ J → J ⊆ X → I = J) : 
  M.basis_of I X :=
hI.basis_of hIX h 

lemma indep.basis (hI : M.indep I) (h : ∀ J, M.indep J → I ⊆ J → I = J) : M.basis I := hI.basis h

lemma basis.indep (h : M.basis B) : M.indep B := h.1 

lemma basis_of.indep (h : M.basis_of B X) : M.indep B := h.1.2 

lemma basis_of.subset (h : M.basis_of B X) : B ⊆ X := h.1.1 

lemma basis.eq_of_supset_indep (h : M.basis B) (hBI : B ⊆ I) (hI : M.indep I) : B = I :=
h.2 hI hBI

lemma basis.not_indep_of_ssupset (hB : M.basis B) (hBX : B ⊂ X) : ¬ M.indep X := 
hB.not_indep_of_lt hBX 

lemma basis_of.ssupset_not_indep (h : M.basis_of B X) (hBY : B ⊂ Y) (hYX : Y ⊆ X) : ¬ M.indep Y := 
h.not_indep_of_lt hBY hYX 

lemma basis_of.eq_of_supset_indep (h : M.basis_of B X) (hBY : B ⊆ Y) (hYX : Y ⊆ X) (hY : M.indep Y): 
  B = Y := 
h.eq_of_le_indep hBY hYX hY 

lemma basis_of.indep_of_subset (hB : M.basis_of B X) (hIB : I ⊆ B)  : M.indep I := 
hB.indep_of_le hIB 

lemma basis.basis_of_univ (hB : M.basis B) : M.basis_of B univ := hB.basis_of_top

lemma basis.indep_of_subset (hB : M.basis B) (hIB : I ⊆ B) : M.indep I := hB.indep_of_le hIB 

lemma basis.not_basis_of_ssupset (hB : M.basis B) (hBX : B ⊂ X) : ¬M.basis X := hB.lt_not_basis hBX

lemma basis.not_basis_of_ssubset (hB : M.basis B) (hXB : X ⊂ B) : ¬M.basis X := 
hB.not_basis_of_lt hXB 

lemma basis_antichain (M : matroid E): is_antichain (⊆) M.basis := M.basis_antichain 

lemma circuit.dep (hC : M.circuit C) : ¬ M.indep C := hC.1 

lemma circuit.indep_of_ssubset (hC : M.circuit C) (hIC : I ⊂ C) : M.indep I := hC.indep_of_lt hIC 

lemma exists_basis_of (M : matroid E) (X : set E) : ∃ I, M.basis_of I X := M.exists_basis_of X

lemma basis_of.basis (hB : M.basis_of B X) (hX : M.spanning X) : M.basis B := hB.basis hX

lemma indep.extend_to_union_basis {I B : set E} (hI: M.indep I) (hB : M.basis B) : 
   ∃ B', M.basis B' ∧ I ⊆ B' ∧ B' ⊆ I ∪ B :=
hI.extend_to_sup_basis hB 

lemma exists_basis (M : matroid E): ∃ B, M.basis B := M.exists_basis

lemma univ_spanning (M : matroid E) : M.spanning univ := M.top_spanning 

lemma indep.extends_to_basis (hI : M.indep I) : ∃ B, I ⊆ B ∧ M.basis B := hI.extends_to_basis

lemma indep_iff_subset_basis : M.indep I ↔ ∃ B, I ⊆ B ∧ M.basis B := 
supermatroid.indep_iff_le_basis

lemma bases_inj {M₁ M₂ : matroid E} (hB : M₁.bases = M₂.bases)  : M₁ = M₂ := 
  by {ext, simp_rw [mem_indep_sets_iff, indep_iff_subset_basis, ←mem_bases_iff, hB]}

end basic 

section dual 

lemma cobases_eq_image_compl_bases (M : matroid E) : 
  M.cobases = compl '' M.bases := 
by {convert (M.basis_antichain.img_compl.max_lower_set_of), simpa [supermatroid.cobases]}

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

def dual (M : matroid E) : matroid E := M.dual 

lemma dual_indep_sets_eq (M : matroid E)  : M.dual.ind = M.coind := rfl 

lemma dual_indep_iff (M : matroid E) (I : set E): M.dual.indep I ↔ M.coindep I := iff.rfl 

lemma dual_basis_iff (M : matroid E) (B : set E) : M.dual.basis B ↔ M.cobasis B := iff.rfl 

lemma dual_bases_eq (M : matroid E) : M.dual.bases = M.cobases := rfl 

@[simp] lemma dual_dual (M : matroid E) : M.dual.dual = M := 
bases_inj (by simp only [dual_bases_eq, cobases_eq_image_compl_bases, compl_compl_image])

end dual 

end matroid 