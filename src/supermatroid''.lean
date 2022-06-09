/-
Copyright (c) 2022 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Peter Nelson.
-/
import tactic 
import order.minimal
import .lattice_intervals'
import order.lattice_intervals
import .weak_compl
import order.upper_lower
import order.modular_lattice

/-!
# supermatroids 

In this file we define a `supermatroid`, namely a nonempty `lower_set` in a `semilattice_sup`
that satisfies certain augmentation axioms; its members are 'independent'. 


## Main content

- `indep`, `dep`, `coindep`, `basis`, `circuit`, `spanning` : predicates of the form `α → Prop`
  for various supermatroid properties. Defining these as predicates enables dot notation, but
  most also have an alternative `set α` version which can work more smoothly with some parts
  of mathlib. 
- `supermatroid.dual` : the dual supermatroid of a supermatroid `M`; its bases are the complements of the bases
  of `M`. 
- `dual_dual`    : duality is idempotent. 

## References


TODO : rank, circuits, theory for finite supermatroids, etc etc. 
-/


universes u v
 
def supermatroid.maximizable {α : Type u} [preorder α] (s : set α) : Prop := 
  ∀ (a ∈ s) b, a ≤ b → (maximals (≤) ((set.Icc a b) ∩ s)).nonempty

def supermatroid.augmentable {α : Type u} [semilattice_sup α] (s : set α) : Prop := 
  ∀ (a ∈ s) b, (a ∉ maximals (≤) s) → (b ∈ maximals (≤) s) → ((set.Ioc a (a ⊔ b)) ∩ s).nonempty 

open set 

@[ext] structure supermatroid (α : Type u) [semilattice_sup α] := 
(indep           : α → Prop)
(ind_nonempty  : ∃ x, indep x ) 
(ind_lower_set : is_lower_set indep)
(ind_augment   : supermatroid.augmentable indep)
(ind_maximize : supermatroid.maximizable indep)

namespace supermatroid 

section basic 

variables {α : Type u} [lattice α] [bounded_order α] {M : supermatroid α} 
  {i j b x y c d r : α}

--def indep (M : supermatroid α) : α → Prop := M.ind

def dep (M : supermatroid α) := λ x,¬ M.indep x 

def basis (M : supermatroid α) : α → Prop := maximals (≤) M.indep

def basis_of (M : supermatroid α) : α → α → Prop := 
  λ b x, b ∈ maximals (≤) (λ Z, Z ≤ x ∧ M.indep Z)

def circuit (M : supermatroid α) : α → Prop := minimals (≤) M.indepᶜ 

def spanning (M : supermatroid α) (x : α) :=  ∃ b, b ≤ x ∧ M.basis b

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

lemma indep.le_basis_of (hi : M.indep i) (hix : i ≤ x) :
  ∃ j, i ≤ j ∧ M.basis_of j x := 
begin
  obtain ⟨j,⟨hj,(hj_ind : M.indep j)⟩,hj_max⟩ := M.ind_maximize i hi x hix, 
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
exists.elim (M.bot_indep.le_basis_of (@bot_le _ _ _ x)) (λ a ha, ⟨a, ha.2⟩)

lemma indep.augment (hi : M.indep i) (hi_nb : ¬M.basis i) (hj : M.basis j) : 
  ∃ i', i < i' ∧ i' ≤ i ⊔ j ∧ M.indep i' := 
begin
  obtain ⟨i',⟨hi'_int, hi'_ind⟩⟩ := M.ind_augment _ hi _ hi_nb hj, 
  exact ⟨i', (mem_Ioc.mpr hi'_int).1, (mem_Ioc.mpr hi'_int).2, hi'_ind⟩, 
end 

lemma indep.le_basis (hi : M.indep i) (hb : M.basis b) : 
   ∃ b', M.basis b' ∧ i ≤ b' ∧ b' ≤ i ⊔ b :=
exists.elim (hi.le_basis_of (@le_sup_left _ _ i b)) 
  (λ b' h, ⟨b',⟨by_contra (λ hb', 
    begin 
      obtain ⟨b'',hb'b'',hb''1,hb''⟩ := h.2.indep.augment hb' hb,
      exact hb'b''.ne (h.2.eq_of_le_indep hb'b''.le 
        (hb''1.trans (sup_le h.2.le le_sup_right)) hb''),
    end),
    h.1,h.2.1.1⟩⟩)

lemma indep.lt_basis (hi : M.indep i) (hi_nb : ¬ M.basis i) (hb : M.basis b) :
  ∃ b', M.basis b' ∧ i < b' ∧ b' ≤ i ⊔ b :=
begin
  obtain ⟨b',hb',h₁,h₂⟩ := hi.le_basis hb, 
  exact ⟨b', hb', lt_of_le_of_ne h₁ (λ h, (hi_nb (h.symm ▸ hb')).elim), h₂⟩, 
end 

lemma basis_of.basis (hb : M.basis_of b x) (hx : M.spanning x) : M.basis b := 
 by_contra (λ h, 
   ((exists.elim hx (λ b' hb', exists.elim (hb.indep.augment h (hb'.2))
   (λ j hj, hb.not_indep_of_lt hj.1 (hj.2.1.trans (sup_le hb.le hb'.1)) hj.2.2 )))))

lemma exists_basis (M : supermatroid α): ∃ b, M.basis b := 
begin
  obtain ⟨b, ⟨-,hb⟩⟩ := M.bot_indep.le_basis_of (@bot_le α _ _ ⊤), 
  exact ⟨b, hb.indep.basis (λ j hj hbj, hb.eq_of_le_indep hbj le_top hj)⟩, 
end 

lemma basis.exists_extension_from (hb : M.basis b) (x : α) : 
  ∃ b', b' ≤ x ⊔ b ∧ M.basis b' ∧ (M.basis_of (b' ⊓ x) x) :=
begin
  obtain ⟨i,hi⟩ := M.exists_basis_of x, 
  obtain ⟨b',⟨hb',bib',hb'i⟩⟩ := hi.indep.le_basis hb,
  refine ⟨b', hb'i.trans (sup_le_sup_right hi.le _) ,hb', (hb'.inf_right_indep _).basis_of
    inf_le_right (λ j hj hj' hjx, hj'.antisymm (le_inf _ hjx))⟩, 
  rwa ←(hi.eq_of_le_indep ((le_inf bib' hi.le).trans hj') hjx hj), 
end 

lemma top_spanning (M : supermatroid α) : M.spanning ⊤ := 
exists.elim (M.exists_basis) (λ b hb, ⟨b,le_top,hb⟩)

lemma indep.extends_to_basis (hi : M.indep i) : 
  ∃ b, i ≤ b ∧ M.basis b := 
by {obtain ⟨b',hb'⟩ := M.exists_basis, obtain ⟨b,hb⟩ := hi.le_basis hb', exact ⟨b,hb.2.1, hb.1⟩}

lemma indep_iff_le_basis : 
  M.indep i ↔ ∃ b, i ≤ b ∧ M.basis b := 
⟨indep.extends_to_basis, λ h, exists.elim h (λ b hi, hi.2.indep_of_le hi.1)⟩

lemma bases_inj {M₁ M₂ : supermatroid α} (hb : M₁.basis = M₂.basis)  : M₁ = M₂ := 
  by {ext, simp_rw [indep_iff_le_basis, hb]}

end basic 

section basis_axioms 

variables {α : Type u} [lattice α] [bounded_order α] {x x' y y' a b b' b₀ c : α}

def satisfies_middle_axiom (B : set α) : Prop := 
  ∀ x x' b b', x ≤ x' → x ≤ b → b' ≤ x' → b ∈ B → b' ∈ B → ∃ b₀ ∈ B, x ≤ b₀ ∧ b₀ ≤ x'

-- infinite axiom 
def satisfies_extension (B : set α) : Prop := 
  ∀ x b y, b ∈ B → x ≤ b → x ≤ y → (maximals (≤) ((Icc x y) ∩ {i | ∃ b' ∈ B, i ≤ b'})).nonempty 

def supermatroid_of_bases {B : set α} 
  (h_nonempty : nonempty B)
  (h_antichain : is_antichain (≤) B) 
  (h_mid : satisfies_middle_axiom B) 
  (h_ext : satisfies_extension B):
  supermatroid α := 
{ indep         := λ x, ∃ b ∈ B, x ≤ b,
  ind_nonempty  := h_nonempty.elim (λ b, ⟨(⊥ : α), ⟨b.1, b.2,bot_le⟩ ⟩),
  ind_lower_set := λ i j hji, by {rintro ⟨b,⟨hb,hib⟩⟩, exact ⟨b,⟨hb,hji.trans hib⟩⟩},
  ind_maximize := by {rintros i ⟨b,⟨hb,hib⟩⟩ b' hib', exact h_ext i b b' hb hib hib'},
  ind_augment   := 
  begin
    rintros i ⟨b,⟨hb,hib⟩⟩ b' hi hb', 
    erw h_antichain.max_lower_set_of at hi hb', 
    obtain ⟨b₀, ⟨hb₀, hib₀, hb₀b⟩⟩ :=  
      h_mid i (i ⊔ b') b b' le_sup_left hib le_sup_right hb hb', 
    exact ⟨b₀,⟨lt_of_le_of_ne hib₀ (λ h, hi (h.symm ▸ hb₀)),hb₀b⟩,b₀,hb₀,rfl.le⟩, 
  end}


lemma bases_satisfy_middle (M : supermatroid α) : satisfies_middle_axiom M.basis :=
begin
  intros x x' b b' hxx' hxb hb'x' hb hb', 
  obtain ⟨b₀,⟨hb₀,hxb₀,hb₀x⟩⟩ := (hb.indep_of_le hxb).le_basis hb', 
  exact ⟨b₀, hb₀, hxb₀, hb₀x.trans (sup_le hxx' hb'x')⟩,
end 


lemma bases_satisfy_extension (M : supermatroid α) : satisfies_extension M.basis :=
begin
  intros x b y hb hxb hxy, 
  obtain ⟨j, hxj, hjy⟩ := (hb.indep_of_le hxb).le_basis_of hxy, 
  obtain ⟨b',⟨hjb',hb'⟩⟩ := hjy.indep.extends_to_basis, 
  refine ⟨j,⟨⟨hxj,hjy.le⟩,⟨b',hb',hjb'⟩⟩, λ a hxa hay,_ ⟩, 
  obtain ⟨b'',hb'',hab''⟩ := hxa.2, 
  exact hjy.eq_of_le_indep hay hxa.1.2 (hb''.indep_of_le hab''), 
end 


end basis_axioms

section dual 

variables {α : Type u} [distrib_lattice α] [is_modular_lattice α] [bounded_order α] [has_precompl α] 
  {M : supermatroid α} {i j b x y c d r : α}

open has_precompl

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

-- lemma coindep.exists_le_pcompl_basis (hi : M.coindep i): ∃ b, M.basis b ∧ disjoint i b := 
--   exists.elim hi (λ b hb, ⟨b, hb.1, disjoint_iff_le_compl_right.mpr hb.2⟩)

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

-- The finite one 
lemma coind_augment (M : supermatroid α) : 
  augmentable M.coindep := 
begin
  rintros i ⟨b, hb_b, hib⟩ j hic_nb hjc_b, 
  rw [←cobasis_iff, cobasis_iff_pcompl_basis] at hic_nb hjc_b,  
   
  obtain ⟨b'',hb''_b,hjb'',hb''ji⟩ := (hjc_b.indep.inf_left_indep iᵒ).le_basis hb_b, 
  
  have hb''_lt_io : b'' < iᵒ, from 
  lt_of_le_of_ne 
    ((hb''ji.trans (sup_le_sup_left (le_pcompl_comm.mp hib) _)).trans (by simp))
    ( λ he, hic_nb ⟨(hic_nb (he.subst hb''_b)).elim, 
      λ a ha hia, by {subst he, exact hb''_b.eq_of_le_indep hia ha}⟩),
     
  refine ⟨b''ᵒ , ⟨lt_pcompl_comm.mp hb''_lt_io, _⟩,⟨b'',hb''_b, rfl.le⟩⟩,
  rwa [pcompl_le_comm, pcompl_sup], 
end 

-- the infinite one 
lemma coind_maximize (M : supermatroid α) : 
  maximizable M.coindep := 
begin
  rintros i₁ ⟨b,hb, hi₁b⟩ x hi₁x,
  obtain ⟨b₁,⟨hb₁x, hb₁, hb₁x'⟩⟩:= hb.exists_extension_from xᵒ, 
  
  rw ←le_pcompl_comm at hi₁b, rw ←pcompl_le_iff at hi₁x,
  refine ⟨x ⊓ b₁ᵒ,
    ⟨⟨le_inf (pcompl_le_iff.mp hi₁x) (le_pcompl_comm.mp (hb₁x.trans (sup_le hi₁x hi₁b))),
      inf_le_left⟩,
    M.coindep_iff.mpr ⟨b₁,hb₁,inf_le_right⟩⟩, λ a ha hxa, le_antisymm hxa (le_inf ha.1.2 _)⟩, 
  
  obtain ⟨⟨hi₁a, hax⟩, ⟨b₂,⟨hb₂,hab₂⟩⟩⟩ := ha, 
  rw [←pcompl_le_iff] at ⊢ hax hxa hab₂, 
  rw [pcompl_inf] at hxa,
  rw pcompl_pcompl at hab₂ ⊢ hxa,
  have hb₁b₂ := hab₂.trans hxa,  
  
  suffices h : b₁ ≤ b₂ ⊔ xᵒ, from h.trans (sup_le hab₂ hax),
  by_contradiction h', 
  
  set i' := (xᵒ ⊓ b₁) ⊔ (b₂ ⊓ b₁) with hi',
  
  have hi'b₁ : i' < b₁ := 
    lt_of_le_of_ne (sup_le inf_le_right inf_le_right) (λ h , h' (by {rw [←h,hi'],
      exact sup_le (inf_le_left.trans le_sup_right) (inf_le_left.trans le_sup_left)})),

  obtain ⟨b₃, ⟨hb₃, hltb₃, hb₃le⟩⟩ := 
    (hb₁.indep_of_le (sup_le inf_le_right inf_le_right) : M.indep i').lt_basis 
      (hb₁.not_basis_of_lt hi'b₁) hb₂, 

  have h₁ := @inf_lt_inf_of_lt_of_sup_le_sup _ _ _ _ _ xᵒ hltb₃ (sup_le _ le_sup_right),  
  { have h₂ : xᵒ ⊓ b₁ ≤ i' ⊓ xᵒ := (le_inf le_sup_left inf_le_left), 
    rw inf_comm at h₂, 
    exact (hb₁x'.not_indep_of_lt (h₂.trans_lt h₁) inf_le_right) (hb₃.inf_right_indep _)},

  rw [sup_assoc, @sup_comm _ _ _ b₂, sup_inf_self, sup_inf_right, le_inf_iff] at hb₃le, 
  rw [sup_right_comm, @sup_comm _ _ _ xᵒ, sup_inf_self, sup_inf_left, le_inf_iff],  
  
  exact ⟨hb₃le.1, hb₃le.2.trans (sup_le le_sup_right hb₁b₂)⟩, 
  -- how do we do this if the lattice is modular but not distributive? Is it possible?
end 

def dual (M : supermatroid α) : supermatroid α := 
{ indep := M.coindep,
  ind_nonempty := M.coindep_nonempty,
  ind_lower_set := M.coindep_lower_set,
  ind_augment := M.coind_augment,
  ind_maximize := M.coind_maximize }

lemma dual_ind_eq (M : supermatroid α)  : M.dual.indep = M.coindep := rfl 

lemma dual_indep_iff (M : supermatroid α) (i : α): M.dual.indep i ↔ M.coindep i := iff.rfl 

lemma dual_basis_iff (M : supermatroid α) (b : α) : M.dual.basis b ↔ M.cobasis b := iff.rfl 

lemma dual_bases_eq (M : supermatroid α) : M.dual.basis = M.cobasis := rfl 

@[simp] lemma dual_dual (M : supermatroid α) : M.dual.dual = M := 
bases_inj (by simp only [dual_bases_eq, cobases_eq_image_pcompl_bases, pcompl_pcompl_image])


end dual 


-- section iso 

-- variables {α : Type u} {β : Type v} [semilattice_sup α] [semilattice_sup β] {M : supermatroid α} 
--   {N : supermatroid β}

-- structure supermatroid_iso (M : supermatroid α) (M' : supermatroid β) : Type (max u v) :=
-- (to_equiv  : α ≃o β)
-- (on_ind : ∀ a, M.ind a ↔ M'.ind (to_equiv a) )

-- infix `≃l` :25 := supermatroid_iso 




-- end iso 

-- section minor



-- variables {α : Type u} [distrib_lattice α] [bounded_order α] {M : supermatroid α} {c d r : α}

-- --def contract {M : supermatroid α} (c : α) (hc : M.indep c) : sorry



-- -- #check supermatroid.circuit M


-- end minor 

end supermatroid 