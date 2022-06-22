/-
Copyright (c) 2022 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Peter Nelson.
-/
import tactic 
import .easy_lemmas
import order.minimal
import order.upper_lower
import order.modular_lattice
import .weak_compl
import order.atoms

/-!
# supermatroids 

In this file we define a `supermatroid`, namely a nonempty `antichain` in a `lattice`
that satisfies certain incrementation axioms; its members are 'independent'. 

## Main content

- `indep`, `dep`, `coindep`, `basis`, `circuit`, `cocircuit`, `spanning` : predicates of the form 
  `α → Prop` for various supermatroid properties. Defining these as predicates rather than set 
  enables dot notation, but sometimes we treat them as sets. 

- the `order_dual` of a supermatroid `M` : If `M` is a matroid on a modular lattice, then `M` is 
  also a matroid relative to the dual order. 
  
## References

-/

universes u v
 
open set 

variables {α : Type u} 

section prelim

variables [preorder α] {s : set α}

def middle (s : set α) : Prop := 
  ∀ x y, x ≤ y → (s ∩ (Ici x)).nonempty → (s ∩ Iic y).nonempty → (s ∩ Icc x y).nonempty  

def max_lower (s : set α) : Prop := 
  ∀ x y, ((lower_closure s) ∩ (Icc x y)).nonempty 
    → (maximals (≤) ((lower_closure s) ∩ (Icc x y))).nonempty

def min_upper (s : set α) : Prop := 
  ∀ x y, ((upper_closure s) ∩ (Icc x y)).nonempty 
    → (minimals (≤) ((upper_closure s) ∩ (Icc x y))).nonempty
  
lemma max_lower_dual (hs : min_upper s) : @max_lower αᵒᵈ _ s := λ x y, by {erw [dual_Icc], apply hs}

lemma min_upper_dual (hs : max_lower s) : @min_upper αᵒᵈ _ s := λ x y, by {erw [dual_Icc], apply hs}

lemma middle_dual (hs : middle s) : @middle αᵒᵈ _ s := 
λ x y h, by {erw [dual_Ici, dual_Iic, dual_Icc], exact flip (hs y x h)}

/-- A `supermatroid` is a nonempty antichain of `bases` in a lattice such that 
  - for all `x ≤ y` such that `x` is below a basis and `y` is above a basis, the closed interval 
    `[x,y]` contains a basis 
  - For all `x,y` such that the interval `[x,y]` contains an element below a basis, this interval
    contains a maximal element that is below a basis. 
-/
@[ext] structure supermatroid (α : Type u) [preorder α] := 
(basis                 : α → Prop)
(exists_basis          : ∃ b, basis b) 
(basis_antichain       : is_antichain (≤) basis)
(basis_has_middle      : middle basis)
(basis_has_max_lower   : max_lower basis)

end prelim 

namespace supermatroid 

variables {i j b b' b'' x y c d r s t : α}

section partial_order 

variables [partial_order α] {M : supermatroid α} 

/-- An element below a basis is independent-/
def indep (M : supermatroid α) (x : α) := ∃ b, M.basis b ∧ x ≤ b 

/-- An element above a basis is spanning-/
def spanning (M : supermatroid α) (x : α) :=  ∃ b, M.basis b ∧ b ≤ x 

/-- An element that is not independent is depedent-/
@[reducible] def dep (M : supermatroid α) (x : α) := ¬ M.indep x 

/-- A basis of `x` is a maximal element subject to being independent and below `x`-/
def basis_of (M : supermatroid α) (i x : α) :=
  M.indep i ∧ i ≤ x ∧ ∀ j, M.indep j → j ≤ x → i ≤ j → i = j 

lemma basis_middle (hxy : x ≤ y) (hb : M.basis b) (hb' : M.basis b') (hxb : x ≤ b) (hb'y : b' ≤ y): 
  ∃ b₀, M.basis b₀ ∧ x ≤ b₀ ∧ b₀ ≤ y :=
M.basis_has_middle _ _ hxy ⟨b,hb,hxb⟩ ⟨b',hb',hb'y⟩

@[simp] lemma mem_lower_set_basis_iff_indep : M.indep i ↔ i ∈ lower_closure M.basis := 
⟨λ ⟨b,hb,hbx⟩, ⟨b,hb,hbx⟩, λ ⟨b,hb,hbx⟩, ⟨b,hb,hbx⟩⟩

lemma indep.indep_of_le (hi : M.indep i) (hji : j ≤ i) : M.indep j := 
exists.elim hi (λ b hb, ⟨b, ⟨hb.1, hji.trans hb.2⟩⟩)

lemma bot_indep [order_bot α] (M : supermatroid α): M.indep ⊥ := 
exists.elim M.exists_basis (λ b h, ⟨b, h, bot_le⟩)

lemma indep.not_dep (hi : M.indep i) : ¬ M.dep i := by rwa [not_not]

lemma dep.not_indep (hx : M.dep x) : ¬ M.indep x := hx 

lemma not_dep_iff_indep : ¬ M.dep i ↔ M.indep i  := by rw [not_not]
  
lemma indep_or_dep (i : α) : M.indep i ∨ M.dep i := em _  

lemma not_indep_iff_dep : ¬ M.indep i ↔ M.dep i := iff.rfl 
  
lemma dep.dep_of_lt (hx : M.dep x) (hxy : x ≤ y) : M.dep y := 
not_indep_iff_dep.mp (λ h, (hx.not_indep (h.indep_of_le hxy)).elim)

lemma indep.basis_of (hi : M.indep i) (hix : i ≤ x) (h : ∀ j, M.indep j → j ≤ x → i ≤ j → i = j) : 
  M.basis_of i x :=
⟨hi,  hix, h⟩

lemma basis.indep (h : M.basis b) : M.indep b := ⟨b, h, rfl.le⟩ 

lemma exists_indep (M : supermatroid α) : ∃ i, M.indep i := 
exists.elim M.exists_basis (λ b hb, ⟨b, hb.indep⟩)

lemma basis.indep_of_le (hb : M.basis b) (hi : i ≤ b) : M.indep i := ⟨b,hb,hi⟩ 

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

lemma basis_iff_maximal_indep : M.basis b ↔ (maximals (≤) M.indep) b := 
⟨λ hb, ⟨hb.indep,λ i hi hbi, hb.eq_of_le_indep hbi hi⟩, 
  by {rintro ⟨⟨b',hb',hbb'⟩, hb''⟩, rwa hb'' hb'.indep hbb'}⟩

lemma basis_of.indep (h : M.basis_of b x) : M.indep b := h.1

lemma basis_of.le (h : M.basis_of b x) : b ≤ x := h.2.1

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

lemma basis.basis_of_top [order_top α] (hb : M.basis b) : M.basis_of b ⊤ := 
hb.indep.basis_of le_top (λ j hj hbj h, hb.eq_of_le_indep h hj) 
    
lemma basis.lt_not_basis (hb : M.basis b) (hbx : b < x) : ¬ M.basis x := 
λ hx, (hb.not_indep_of_lt hbx hx.indep)

lemma basis.not_basis_of_lt (hb : M.basis b) (hxb : x < b) : ¬ M.basis x := 
λ h, (h.lt_not_basis hxb) hb 

lemma indep.basis (hi : M.indep i) (hmax : ∀ j, M.indep j → i ≤ j → i = j) : M.basis i := 
by {obtain ⟨b,hb, hbi⟩ := hi, have := (hmax b hb.indep hbi), rwa ← this at hb}

lemma indep.increment (hi : M.indep i) (hi_nb : ¬M.basis i) (his : i ≤ s) (hs : M.spanning s):
  ∃ j, i < j ∧ j ≤ s ∧ M.indep j := 
begin
  obtain ⟨⟨bi, hbi, hibi⟩,⟨bs,hbs,hsbs⟩⟩ := ⟨hi,hs⟩,  
  obtain ⟨b, hb, hib, hbs⟩ := basis_middle his hbi hbs hibi hsbs, 
  exact ⟨b, hib.lt_of_ne' (λ h, hi_nb (h ▸ hb)),hbs,hb.indep⟩, 
end 

lemma basis_of.basis (hb : M.basis_of b x) (hx : M.spanning x) : M.basis b := 
begin
  by_contradiction h, 
  obtain ⟨j,hbj,hjx,hj⟩ := hb.indep.increment h hb.le hx, 
  exact hb.not_indep_of_lt hbj hjx hj, 
end 

lemma exists_basis_of [order_bot α] (M : supermatroid α) (x : α) : ∃ i, M.basis_of i x :=
begin
  obtain ⟨b,hb⟩ := M.exists_basis, 
  obtain ⟨i,⟨⟨b,hb,hib⟩,-,hix⟩,hi'⟩ := M.basis_has_max_lower ⊥ x ⟨⊥,⟨b,hb,bot_le⟩,rfl.le, bot_le⟩, 
  exact ⟨i,⟨b,hb,hib⟩,hix, λ j hj hjx hij, hi' 
    ⟨(mem_lower_set_basis_iff_indep.mp hj),⟨bot_le, hjx⟩⟩ hij⟩, 
end 

lemma bases_inj {M₁ M₂ : supermatroid α} (hb : M₁.basis = M₂.basis)  : M₁ = M₂ := by {ext, rw hb}

lemma indep_inj {M₁ M₂ : supermatroid α} (hb : M₁.indep = M₂.indep)  : M₁ = M₂ := 
by {ext, simp_rw [basis_iff_maximal_indep, hb]}

lemma basis_of_indep_spanning (hi : M.indep x) (hs : M.spanning x) : M.basis x := 
begin 
  obtain ⟨⟨bi,hbi,hxbi⟩,⟨bs,hbs,hbsx⟩⟩ := ⟨hi,hs⟩, 
  refine by_contra (λ h, (M.basis_antichain hbs hbi (λ h', h _) (hbsx.trans hxbi)).elim), 
  subst h', rwa (hxbi.antisymm hbsx), 
end 

end partial_order

section lattice

variables [lattice α] {M : supermatroid α}

lemma indep.inf_left_indep (hi : M.indep i) (x : α) : M.indep (x ⊓ i) := 
hi.indep_of_le inf_le_right

lemma indep.inf_right_indep (hi : M.indep i) (x : α) : M.indep (i ⊓ x) := 
hi.indep_of_le inf_le_left

lemma basis.inf_left_indep (hb : M.basis b) (x : α) : M.indep (x ⊓ b) := 
hb.indep.indep_of_le inf_le_right

lemma basis.inf_right_indep (hb : M.basis b) (x : α) : M.indep (b ⊓ x) := 
hb.indep.indep_of_le inf_le_left

/-- An alternative version of `exists_basis_of` that assumes `lattice` rather than `order_bot` -/
lemma exists_basis_of' (M : supermatroid α) (x : α) : ∃ i, M.basis_of i x := 
begin
  obtain ⟨b,hb⟩ := M.exists_basis, 
  obtain ⟨i,⟨⟨b,hb,hib⟩,h',hix⟩,hi'⟩ := 
    M.basis_has_max_lower (x ⊓ b) x ⟨x ⊓ b, ⟨b,hb,inf_le_right⟩, rfl.le,inf_le_left⟩, 
  exact ⟨i,⟨b,hb,hib⟩,hix, λ j hj hjx hij, 
    hi' ⟨(mem_lower_set_basis_iff_indep.mp hj), h'.trans hij,hjx⟩ hij⟩, 
end 

lemma indep.increment_sup (hi : M.indep i) (hi_nb : ¬M.basis i) (hb : M.basis b) : 
  ∃ i', i < i' ∧ i' ≤ i ⊔ b ∧ M.indep i' := 
begin
  obtain ⟨b₁, hb₁, hib₁⟩ := hi, 
  obtain ⟨b₂, hb₂, hib₂, hb₂i⟩ := basis_middle (le_sup_left : i ≤ i ⊔ b) hb₁ hb hib₁ le_sup_right, 
  exact ⟨b₂, lt_of_le_of_ne' hib₂ (λ h, hi_nb (h ▸ hb₂)), hb₂i, hb₂.indep⟩, 
end 

lemma basis.max_inf (hb : M.basis b) (x : α): 
  ∃ b', M.basis b' ∧ b ⊓ x ≤ b' ∧ ∀ b'', M.basis b'' → b' ⊓ x ≤ b'' → b' ⊓ x = b'' ⊓ x :=
begin
  obtain ⟨i,⟨⟨b₁,hb₁,hib₁⟩,hbi,hix⟩,hmax⟩ := M.basis_has_max_lower _ x 
    ⟨b ⊓ x, ⟨⟨b,hb,inf_le_left⟩,⟨rfl.le,inf_le_right⟩⟩⟩, 
  
  refine ⟨b₁,hb₁,hbi.trans hib₁, λ b₂ hb₂ hb₁b₂, inf_eq_inf_of_le_of_le hb₁b₂ _⟩, 
  have hib₂ := (le_inf hib₁ hix).trans hb₁b₂,
  rwa ←hmax ⟨⟨b₂,hb₂,(inf_le_left : b₂ ⊓ x ≤ b₂)⟩, 
    ⟨le_inf (hbi.trans hib₂) inf_le_right ,inf_le_right⟩⟩ (le_inf hib₂ hix), 
end 

lemma indep.le_basis_of (hi : M.indep i) (hix : i ≤ x) :
  ∃ j, i ≤ j ∧ M.basis_of j x := 
begin
  obtain ⟨b,hb,hbi⟩ := hi, 
  obtain ⟨b',⟨hb',hb'x,hb'_max⟩⟩ := hb.max_inf x, 
  refine ⟨b' ⊓ x, le_inf ((le_inf hbi hix).trans hb'x) hix, hb'.inf_right_indep _,inf_le_right, _⟩, 
  rintros j ⟨b'',hb'',hjb''⟩ hjx hb'j, 
  have h₀ := (le_inf hjb'' hjx), 
  rw [←(hb'_max _ hb'' (hb'j.trans hjb''))] at h₀, 
  exact le_antisymm hb'j h₀, 
end 

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

lemma basis.inf_basis_of (hb : M.basis b) (x : α) : 
  ∃ b', b' ≤ x ⊔ b ∧ M.basis b' ∧ (M.basis_of (b' ⊓ x) x) :=
begin
  obtain ⟨i,hi⟩ := M.exists_basis_of' x, 
  obtain ⟨b',⟨hb',bib',hb'i⟩⟩ := hi.indep.le_basis_sup hb,
  refine ⟨b', hb'i.trans (sup_le_sup_right hi.le _) ,hb', 
    (hb'.inf_right_indep _).basis_of inf_le_right (λ j hj hjx hb'j, hb'j.antisymm (le_inf _ hjx))⟩,
  rwa ←hi.eq_of_le_indep (le_trans (le_inf bib' hi.le) hb'j) hjx hj,  
end 

lemma basis.lt_basis_sup (hb : M.basis b) (hib : i < b) (hb' : M.basis b'):
  ∃ b₀, M.basis b₀ ∧ i < b₀ ∧ b₀ ≤ i ⊔ b' :=
(hb.indep_of_le hib.le).lt_basis_sup (hb.not_basis_of_lt hib) hb' 

end lattice

section dual 

variables [lattice α] [is_modular_lattice α]

lemma basis_has_min_upper (M : supermatroid α) : min_upper M.basis := 
begin
  rintros x y ⟨s,⟨b,hb,hbs⟩,hxs,hsy⟩, 
  obtain ⟨b₁,hb₁b,hb₁,hb₁x⟩ := hb.inf_basis_of x, 
  refine ⟨x ⊔ b₁,⟨⟨b₁,hb₁,le_sup_right⟩,le_sup_left,sup_le (hxs.trans hsy) 
    (hb₁b.trans ((sup_le hxs hbs).trans hsy))⟩, _⟩, 
  
  rintros t ⟨⟨b₂,hb₂,hb₂t⟩,hxt,hty⟩ htx,  
  refine le_antisymm (sup_le hxt _) htx,
  by_contradiction hb₁t, 
  set j := b₁ ⊓ (x ⊔ b₂) with hj, 

  have hj_lt : j < b₁ := inf_le_left.lt_of_ne 
    (λ h_eq, hb₁t (by {rw ← h_eq, exact inf_le_right.trans (sup_le hxt hb₂t)})), 

  obtain ⟨b₃, hb₃, hjb₃, hb₃j⟩ := hb₁.lt_basis_sup hj_lt hb₂, 
  
  have h1 := @inf_lt_inf_of_lt_of_sup_le_sup _ _ _ _ _ x hjb₃ (sup_le _ le_sup_right), 
  swap, 
  { rw [hj, inf_comm, inf_sup_assoc_of_le b₁ le_sup_right, le_inf_iff] at hb₃j, 
    rw [hj, inf_comm, inf_sup_assoc_of_le b₁ le_sup_left, le_inf_iff], 
    refine ⟨hb₃j.1, hb₃j.2.trans (sup_le le_sup_left (hb₂t.trans _))⟩,
    rwa sup_comm},
  refine (hb₁x.not_indep_of_lt (lt_of_le_of_lt (le_inf _ inf_le_right) h1) 
    inf_le_right (hb₃.inf_right_indep x)), 
  rw [hj, inf_comm, @inf_comm _ _ _ (x ⊔ b₂)], 
  exact le_inf (inf_le_left.trans le_sup_left) inf_le_right,  
end 

/-- The matroid on the dual lattice with the same set of bases as `M`-/
def order_dual (M:  supermatroid α) : supermatroid αᵒᵈ :=  
{ basis := M.basis,
  exists_basis := M.exists_basis,
  basis_antichain := M.basis_antichain.to_dual,
  basis_has_middle := middle_dual M.basis_has_middle,
  basis_has_max_lower := max_lower_dual M.basis_has_min_upper}

postfix `ᵈ`:(max + 1) := order_dual 

open has_involution

def dual [has_involution α] (M : supermatroid α) : supermatroid α := 
{ basis := invo ⁻¹' M.basis, 
  exists_basis := exists.elim M.exists_basis 
    (λ b hb, ⟨bᵒ, by rwa [mem_preimage_invo', invo_invo]⟩),
  basis_antichain := preimage_antichain M.basis_antichain, 
  basis_has_middle := 
  begin
    intros x y hxy, 
    
    simp only [←image_invo_eq_preimage_invo, image_inter_nonempty_iff, preimage_Ici, 
      preimage_Iic, preimage_Icc], 
    exact flip (M.basis_has_middle yᵒ xᵒ (invo_le_iff.mpr hxy)), 
  end, 
  basis_has_max_lower := 
  begin
    intros x y h, 
    simp only [←image_invo_eq_preimage_invo, lower_closure_image_invo,image_inter_nonempty_iff, 
      preimage_Icc] at h, 
    
    obtain ⟨a,⟨h₁,h₂⟩,h₃⟩ := M.basis_has_min_upper yᵒ xᵒ h, 
    rw [lower_closure_preimage_invo], 
    refine ⟨aᵒ, ⟨by rwa [mem_preimage, invo_invo],by rwa [←mem_image_invo, image_Icc]⟩,_⟩,
    rintros p ⟨hp1,hp2⟩ hap, 
    rw [←invo_invo p, ←mem_image_invo, image_Icc] at hp2, 
    rw [(h₃ ⟨hp1,hp2⟩ (invo_le_comm.mp hap)), invo_invo], 
  end, 

}



end dual 

section spanning

variables [lattice α] [is_modular_lattice α] {M : supermatroid α}

/-- A super of `x` is a minimal element subject to being spanning and above `x`-/
def super_of (M : supermatroid α) (s x : α) := @basis_of αᵒᵈ _ Mᵈ s x

@[simp] lemma mem_upper_set_basis_iff_spanning : M.spanning s ↔ s ∈ upper_closure M.basis := 
⟨λ ⟨b,hb,hbx⟩, ⟨b,hb,hbx⟩, λ ⟨b,hb,hbx⟩, ⟨b,hb,hbx⟩⟩

lemma super_of_iff : 
  M.super_of s x ↔ M.spanning s ∧ x ≤ s ∧ ∀ s', M.spanning s' → x ≤ s' → s' ≤ s → s = s' := iff.rfl 

lemma spanning.super_of (hs : M.spanning s) (hxs : x ≤ s) 
  (h : ∀ t, M.spanning t → x ≤ t → t ≤ s → s = t) : M.super_of s x :=
⟨hs, hxs, h⟩

lemma spanning.spanning_of_le (hs : M.spanning s) (hst : s ≤ t) : M.spanning t := 
exists.elim hs (λ b hb, ⟨b, hb.1, hb.2.trans hst⟩)

lemma basis.spanning (h : M.basis b) : M.spanning b := ⟨b, h, rfl.le⟩

lemma basis.spanning_of_le (h : M.basis b) (hbs : b ≤ s) : M.spanning s := 
  h.spanning.spanning_of_le hbs 

lemma basis_iff_minimal_spanning : M.basis b ↔ (minimals (≤) M.spanning) b :=
@basis_iff_maximal_indep _ _ _ Mᵈ 

lemma super_of.spanning (h : M.super_of s x) : M.spanning s := h.1 

lemma super_of.le (h : M.super_of s x) : x ≤ s := h.2.1 

lemma super_of.eq_of_spanning_le (hs : M.super_of s x) (hxt : x ≤ t) (hts : t ≤ s) 
  (ht : M.spanning t) : t = s := 
(hs.2.2 _ ht hxt hts).symm

lemma super_of.not_spanning_of_lt (hs : M.super_of s x) (hts : t < s) (hxt : x ≤ t):
  ¬ M.spanning t := 
λ h, hts.ne (hs.eq_of_spanning_le hxt hts.le h)

lemma top_spanning [order_top α] (M : supermatroid α) : M.spanning ⊤ := 
exists.elim (M.exists_basis) (λ b hb, ⟨b,hb,le_top⟩)

lemma exists_super_of [order_top α] (M : supermatroid α) (x : α) : ∃ s, M.super_of s x :=
@exists_basis_of αᵒᵈ _ _ Mᵈ x

lemma spanning.decrement (hs : M.spanning s) (hs_nb : ¬M.basis s) (his : i ≤ s) (hi : M.indep i): 
  ∃ t, t < s ∧ i ≤ t ∧ M.spanning t := 
@indep.increment αᵒᵈ s i _ Mᵈ hs hs_nb his hi

lemma spanning.sup_left_spanning (hs : M.spanning s) (x : α) : M.spanning (x ⊔ s) := 
  hs.spanning_of_le le_sup_right

lemma spanning.sup_right_spanning (hs : M.spanning s) (x : α) : M.spanning (s ⊔ x) := 
  hs.spanning_of_le le_sup_left

lemma basis.sup_left_spanning (h : M.basis b) (x : α) : M.spanning (x ⊔ b) := 
  h.spanning.sup_left_spanning _ 

lemma basis.sup_right_spanning (h : M.basis b) (x : α) : M.spanning (b ⊔ x) := 
  h.spanning.sup_right_spanning _ 

lemma spanning.decrement_inf (hs : M.spanning s) (hs_nb : ¬M.basis s) (hb : M.basis b) : 
  ∃ t, t < s ∧ s ⊓ b ≤ t ∧ M.spanning t := 
@indep.increment_sup αᵒᵈ _ _ _ Mᵈ hs hs_nb hb 

lemma super_of.basis (hs : M.super_of s x) (hx : M.indep x) : M.basis s :=
@basis_of.basis αᵒᵈ _ _ _ Mᵈ hs hx

lemma basis.min_sup (hb : M.basis b) (x : α) : 
  ∃ b', M.basis b' ∧ b' ≤ b ⊔ x ∧ ∀ b'', M.basis b'' → b'' ≤ b' ⊔ x → b' ⊔ x = b'' ⊔ x :=
@basis.max_inf αᵒᵈ _ _ Mᵈ hb x 

lemma spanning.super_of_le (hs : M.spanning s) (hxs : x ≤ s) : 
  ∃ t, t ≤ s ∧ M.super_of t x :=
@indep.le_basis_of αᵒᵈ _ _ _ Mᵈ hs hxs

lemma spanning.basis_inf_le (hs : M.spanning s) (hb : M.basis b) :
  ∃ b', M.basis b' ∧ b' ≤ s ∧ s ⊓ b ≤ b' := 
@indep.le_basis_sup αᵒᵈ _ _ _ Mᵈ hs hb 

lemma spanning.basis_inf_lt (hs : M.spanning s) (hs_nb : ¬ M.basis s) (hb : M.basis b) :
  ∃ b', M.basis b' ∧ b' < s ∧ s ⊓ b ≤ b' := 
@indep.lt_basis_sup αᵒᵈ _ _ _ Mᵈ hs hs_nb hb 

lemma basis.basis_inf_lt (hb : M.basis b) (hbs : b < s) (hb' : M.basis b'): 
  ∃ b₀, M.basis b₀ ∧ b₀ < s ∧ s ⊓ b' ≤ b₀ := 
(hb.spanning_of_le hbs.le).basis_inf_lt (hb.lt_not_basis hbs) hb'

lemma basis.sup_super_of (hb : M.basis b) (x : α) :
  ∃ b', x ⊓ b ≤ b' ∧ M.basis b' ∧ M.super_of (b' ⊔ x) x  :=
@basis.inf_basis_of αᵒᵈ _ _ Mᵈ hb x

end spanning 

end supermatroid 