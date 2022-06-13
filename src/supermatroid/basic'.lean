/-
Copyright (c) 2022 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Peter Nelson.
-/
import tactic 
import order.minimal
import order.upper_lower
import order.modular_lattice

/-!
# supermatroids 

In this file we define a `supermatroid`, namely a nonempty `lower_set` in a `semilattice_sup`
that satisfies certain augmentation axioms; its members are 'independent'. 


## Main content

- `indep`, `dep`, `coindep`, `basis`, `circuit`, `spanning` : predicates of the form `α → Prop`
  for various supermatroid properties. Defining these as predicates rather than set enables dot 
  notation, but sometimes we treat them as sets. 


## References


TODO : rank, circuits, theory for finite supermatroids, etc etc. -/

universes u v
 
-- -- the infinite axioms
-- def supermatroid.maximizable {α : Type u} [preorder α] (s : set α) : Prop := 
--   ∀ (a ∈ s) b, a ≤ b → (maximals (≤) ((set.Icc a b) ∩ s)).nonempty

-- -- augmentation axiom 
-- def supermatroid.augmentable {α : Type u} [semilattice_sup α] (s : set α) : Prop := 
--   ∀ (a ∈ s) b, (a ∉ maximals (≤) s) → (b ∈ maximals (≤) s) → ((set.Ioc a (a ⊔ b)) ∩ s).nonempty 

def supermatroid.satisfies_middle_axiom {α : Type u} [preorder α] (s : set α) : Prop := 
  ∀ x x' (b ∈ s) (b' ∈ s), x ≤ x' → x ≤ b → b' ≤ x' → ∃ b₀ ∈ s, x ≤ b₀ ∧ b₀ ≤ x'

def supermatroid.max_inf {α : Type u} [lattice α] (s : set α) : Prop := 
  ∀ x (b ∈ s), ∃ b' ∈ s, b ⊓ x ≤ b' ⊓ x ∧ ∀ (b'' ∈ s), b' ⊓ x ≤ b'' ⊓ x → b' ⊓ x = b'' ⊓ x

def supermatroid.max_sup {α : Type u} [lattice α] (s : set α) : Prop := 
  ∀ x (b ∈ s), ∃ b' ∈ s, b ⊔ x ≤ b' ⊔ x ∧ ∀ (b'' ∈ s), b' ⊔ x ≤ b'' ⊔ x → b' ⊔ x = b'' ⊔ x

open set 

-- 'self-dual' set of basis axioms 
@[ext] structure supermatroid (α : Type u) [lattice α] := 
(basis           : α → Prop)
(basis_nonempty  : ∃ b, basis b) 
(basis_antichain : is_antichain (≤) basis)
(basis_middle    : supermatroid.satisfies_middle_axiom basis)
(basis_max_inf   : supermatroid.max_inf basis)
(basis_max_sup   : supermatroid.max_sup basis)

namespace supermatroid 

section basic 

variables {α : Type u} [lattice α] [bounded_order α] {M : supermatroid α} 
  {i j b x y c d r s : α}

def indep (M : supermatroid α) (x : α) := ∃ b, M.basis b ∧ x ≤ b 

def dep (M : supermatroid α) (x : α) := ¬ M.indep x 

def basis_of (M : supermatroid α) (i x : α) :=
  M.indep i ∧ i ≤ x ∧ ∀ j, M.indep j → j ≤ x → i ≤ j → i = j 

def circuit (M : supermatroid α) : α → Prop := minimals (≤) M.indepᶜ 

def spanning (M : supermatroid α) (x : α) :=  ∃ b, M.basis b ∧ b ≤ x 

lemma indep.indep_of_le (hi : M.indep i) (hji : j ≤ i) : M.indep j := 
exists.elim hi (λ b hb, ⟨b, ⟨hb.1, hji.trans hb.2⟩⟩)

lemma indep.inf_left_indep (hi : M.indep i) (x : α) : M.indep (x ⊓ i) := 
hi.indep_of_le inf_le_right

lemma indep.inf_right_indep (hi : M.indep i) (x : α) : M.indep (i ⊓ x) := 
hi.indep_of_le inf_le_left

lemma bot_indep (M : supermatroid α): M.indep ⊥ := 
exists.elim M.basis_nonempty (λ b h, ⟨b, h, bot_le⟩)

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

lemma indep.basis_of (hi : M.indep i) (hix : i ≤ x) (h : ∀ j, M.indep j → j ≤ x → i ≤ j → i = j) : 
  M.basis_of i x :=
⟨hi,  hix, h⟩

lemma basis.indep (h : M.basis b) : M.indep b := ⟨b, h, rfl.le⟩ 

lemma basis_of.indep (h : M.basis_of b x) : M.indep b := h.1

lemma basis_of.le (h : M.basis_of b x) : b ≤ x := h.2.1

lemma basis.indep_of_le (hb : M.basis b) (hi : i ≤ b) : M.indep i := ⟨b,hb,hi⟩ 

lemma basis.inf_left_indep (hb : M.basis b) (x : α) : M.indep (x ⊓ b) := 
hb.indep.indep_of_le inf_le_right

lemma basis.inf_right_indep (hb : M.basis b) (x : α) : M.indep (b ⊓ x) := 
hb.indep.indep_of_le inf_le_left

lemma basis.eq_of_le_indep (h : M.basis b) (hbi : b ≤ i) (hi : M.indep i) : b = i := 
begin
  by_contradiction h_ne, 
  obtain ⟨b',h₁,h₂⟩ := hi, 
  exact M.basis_antichain h h₁ (λ hbb', h_ne (le_antisymm hbi (hbb'.symm ▸ h₂))) (hbi.trans h₂),
end 

lemma basis.not_indep_of_lt (hb : M.basis b) (hbx : b < x) : ¬ M.indep x := 
λ hx,hbx.ne (hb.eq_of_le_indep hbx.le hx)

lemma basis.eq_of_basis_le (hb : M.basis b) (hx : M.basis x) (hxb : x ≤ b) : x = b :=
hx.eq_of_le_indep hxb hb.indep 

lemma basis_iff_maximal_indep :
  M.basis b ↔ (maximals (≤) M.indep) b := 
begin
  refine ⟨λ hb, ⟨hb.indep,λ i hi hbi, hb.eq_of_le_indep hbi hi⟩, _⟩, 
  rintro ⟨⟨b',hb',hbb'⟩, hb''⟩, 
  rwa hb'' hb'.indep hbb', 
end 

lemma basis_of.not_indep_of_lt (h : M.basis_of b x) (hby : b < y) (hyx : y ≤ x) : ¬ M.indep y := 
begin
  rintros ⟨b',hb',hyb'⟩, 
  obtain ⟨i,hix,hi⟩ := h, 
  exact hby.ne (hi y (hb'.indep_of_le hyb') hyx hby.le), 
end 

lemma basis_of.eq_of_le_indep (h : M.basis_of b x) (hby : b ≤ y) (hYx : y ≤ x) (hy : M.indep y): 
  b = y := 
by_contra (λ h', h.not_indep_of_lt (lt_of_le_of_ne hby h') hYx hy)

lemma basis_of.indep_of_le (hb : M.basis_of b x) (hib : i ≤ b)  : M.indep i := 
(hb.indep).indep_of_le hib 

lemma basis.basis_of_top (hb : M.basis b) : M.basis_of b ⊤ := 
hb.indep.basis_of le_top (λ j hj hbj h, hb.eq_of_le_indep h hj) 
    
lemma basis.lt_not_basis (hb : M.basis b) (hbx : b < x) : ¬ M.basis x := 
λ hx, (hb.not_indep_of_lt hbx hx.indep)

lemma basis.not_basis_of_lt (hb : M.basis b) (hxb : x < b) : ¬ M.basis x := 
λ h, (h.lt_not_basis hxb) hb 

lemma indep.basis (hi : M.indep i) (hmax : ∀ j, M.indep j → i ≤ j → i = j) : M.basis i := 
by {obtain ⟨b,hb, hbi⟩ := hi, have := (hmax b hb.indep hbi), rwa ← this at hb}

lemma indep.le_basis_of (hi : M.indep i) (hix : i ≤ x) :
  ∃ j, i ≤ j ∧ M.basis_of j x := 
begin
  obtain ⟨b,hb,hbi⟩ := hi, 
  obtain ⟨b',⟨hb',hb'x,hb'_max⟩⟩ := M.basis_max_inf x _ hb, 
  refine ⟨b' ⊓ x, (le_inf hbi hix).trans hb'x, hb'.inf_right_indep _,inf_le_right, _⟩, 
  rintros j ⟨b'',hb'',hjb''⟩ hjx hb'j, 
  refine hb'j.antisymm _, 
  rw hb'_max b'' hb'' (le_inf (hb'j.trans hjb'') inf_le_right), 
  exact le_inf hjb'' hjx,
end 

lemma circuit.not_indep (hc : M.circuit c) : ¬ M.indep c := hc.1 

lemma circuit.dep (hc : M.circuit c) : M.dep c := hc.1 

lemma circuit.indep_of_lt (hC : M.circuit c) (hiC : i < c) : M.indep i := 
  by_contra (λ h, (hiC.ne.symm) (hC.2 h hiC.le))

lemma exists_basis_of (M : supermatroid α) (x : α) : ∃ i, M.basis_of i x :=
exists.elim (M.bot_indep.le_basis_of (@bot_le _ _ _ x)) (λ a ha, ⟨a, ha.2⟩)

lemma indep.augment (hi : M.indep i) (hi_nb : ¬M.basis i) (hb : M.basis b) : 
  ∃ i', i < i' ∧ i' ≤ i ⊔ b ∧ M.indep i' := 
begin
  obtain ⟨b₁, hb₁, hib₁⟩ := hi, 
  obtain ⟨b₂, hb₂, hib₂, hb₂i⟩ := M.basis_middle i (i ⊔ b) _ hb₁ _ hb le_sup_left hib₁ le_sup_right, 
  exact ⟨b₂, lt_of_le_of_ne' hib₂ (λ h, hi_nb (h ▸ hb₂)), hb₂i, hb₂.indep⟩, 
end 

lemma basis_of.basis (hb : M.basis_of b x) (hx : M.spanning x) : M.basis b := 
 by_contra (λ h, 
   ((exists.elim hx (λ b' hb', exists.elim (hb.indep.augment h (hb'.1))
   (λ j hj, hb.not_indep_of_lt hj.1 (hj.2.1.trans (sup_le hb.le hb'.2)) hj.2.2 )))))

lemma indep.le_basis_sup (hi : M.indep i) (hb : M.basis b) : 
   ∃ b', M.basis b' ∧ i ≤ b' ∧ b' ≤ i ⊔ b :=
begin
  obtain ⟨b',hib', hb'⟩ := hi.le_basis_of (@le_sup_left _ _ i b), 
  exact ⟨b',hb'.basis ⟨b,hb,le_sup_right⟩, hib', hb'.le⟩, 
end 

lemma indep.lt_basis_sup (hi : M.indep i) (hi_nb : ¬ M.basis i) (hb : M.basis b) :
  ∃ b', M.basis b' ∧ i < b' ∧ b' ≤ i ⊔ b :=
begin
  obtain ⟨b',hb',h₁,h₂⟩ := hi.le_basis_sup hb, 
  exact ⟨b', hb', lt_of_le_of_ne h₁ (λ h, (hi_nb (h.symm ▸ hb')).elim), h₂⟩, 
end 

lemma exists_basis (M : supermatroid α): ∃ b, M.basis b := 
begin
  obtain ⟨b, ⟨-,hb⟩⟩ := M.bot_indep.le_basis_of (@bot_le α _ _ ⊤), 
  exact ⟨b, hb.indep.basis (λ j hj hbj, hb.eq_of_le_indep hbj le_top hj)⟩, 
end 

lemma basis.exists_extension_from (hb : M.basis b) (x : α) : 
  ∃ b', b' ≤ x ⊔ b ∧ M.basis b' ∧ (M.basis_of (b' ⊓ x) x) :=
begin
  obtain ⟨i,hi⟩ := M.exists_basis_of x, 
  obtain ⟨b',⟨hb',bib',hb'i⟩⟩ := hi.indep.le_basis_sup hb,
  refine ⟨b', hb'i.trans (sup_le_sup_right hi.le _) ,hb', 
    (hb'.inf_right_indep _).basis_of inf_le_right (λ j hj hjx hb'j, hb'j.antisymm (le_inf _ hjx))⟩,
  rwa ←hi.eq_of_le_indep (le_trans (le_inf bib' hi.le) hb'j) hjx hj,  
end 

lemma top_spanning (M : supermatroid α) : M.spanning ⊤ := 
exists.elim (M.exists_basis) (λ b hb, ⟨b,hb,le_top⟩)

lemma indep.le_basis (hi : M.indep i) : 
  ∃ b, i ≤ b ∧ M.basis b := 
by {obtain ⟨b',hb'⟩ := M.exists_basis, obtain ⟨b,hb⟩ := hi.le_basis_sup hb', exact ⟨b,hb.2.1, hb.1⟩}

lemma indep.lt_basis (hi : M.indep i) (hi_nb : ¬ M.basis i):
  ∃ b, i < b ∧ M.basis b := 
exists.elim hi.le_basis 
  (λ b hb, by {refine ⟨b, lt_of_le_of_ne' hb.1 (λ h, hi_nb (h ▸ hb.2)), hb.2⟩, } )

lemma indep_iff_le_basis : 
  M.indep i ↔ ∃ b, i ≤ b ∧ M.basis b := 
⟨indep.le_basis, λ h, exists.elim h (λ b hi, hi.2.indep_of_le hi.1)⟩

lemma bases_inj {M₁ M₂ : supermatroid α} (hb : M₁.basis = M₂.basis)  : M₁ = M₂ := by {ext, rw hb}

lemma indep_inj {M₁ M₂ : supermatroid α} (hb : M₁.indep = M₂.indep)  : M₁ = M₂ := 
by {ext, simp_rw [basis_iff_maximal_indep, hb]}

end basic 


end supermatroid 