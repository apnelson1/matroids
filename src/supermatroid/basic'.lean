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

/-!
# supermatroids 

In this file we define a `supermatroid`, namely a nonempty `antichain` in a `lattice`
that satisfies certain incrementation axioms; its members are 'independent'. 


## Main content

- `indep`, `dep`, `coindep`, `basis`, `circuit`, `cocircuit`, `spanning` : predicates of the form 
  `α → Prop` for various supermatroid properties. Defining these as predicates rather than set 
  enables dot notation, but sometimes we treat them as sets. 


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
  ∀ x (b ∈ s), ∃ b' ∈ s, b ⊓ x ≤ b' ∧ ∀ (b'' ∈ s), b' ⊓ x ≤ b'' → b' ⊓ x = b'' ⊓ x

def supermatroid.min_sup {α : Type u} [lattice α] (s : set α) : Prop := 
  ∀ x (b ∈ s), ∃ b' ∈ s, b' ≤ b ⊔ x ∧ ∀ (b'' ∈ s), b'' ≤ b' ⊔ x → b' ⊔ x = b'' ⊔ x

open set 

-- 'self-dual' set of basis axioms 
@[ext] structure supermatroid (α : Type u) [lattice α] := 
(basis           : α → Prop)
(exists_basis    : ∃ b, basis b) 
(basis_antichain : is_antichain (≤) basis)
(basis_middle    : supermatroid.satisfies_middle_axiom basis)
(basis_max_inf   : supermatroid.max_inf basis)
--(basis_min_sup   : supermatroid.min_sup basis)

namespace supermatroid 

variables {α : Type u} [lattice α] {M : supermatroid α} 
  {i j b b' b'' x y c d r s t : α}

section basic 

/-- An element below a basis is independent-/
def indep (M : supermatroid α) (x : α) := ∃ b, M.basis b ∧ x ≤ b 

/-- An element that is not independent is depedent-/
def dep (M : supermatroid α) (x : α) := ¬ M.indep x 

/-- A basis of `x` is a maximal element subject to being independent below `x`-/
def basis_of (M : supermatroid α) (i x : α) :=
  M.indep i ∧ i ≤ x ∧ ∀ j, M.indep j → j ≤ x → i ≤ j → i = j 

/-- A circuit is a minimal dependent element-/
def circuit (M : supermatroid α) : α → Prop := minimals (≤) M.indepᶜ 

/-- An element above a basis is spanning-/
def spanning (M : supermatroid α) (x : α) :=  ∃ b, M.basis b ∧ b ≤ x 

/-- A cocircuit is a maximally nonspanning element-/
def cocircuit (M : supermatroid α) : α → Prop := maximals (≤) M.spanningᶜ

/-- A super of `x` is a minimal element subject to being spanning and above `x`-/
def super_of (M : supermatroid α) (s x : α) := 
  M.spanning s ∧ x ≤ s ∧ ∀ s', M.spanning s' → x ≤ s' → s' ≤ s → s' = s

lemma indep.indep_of_le (hi : M.indep i) (hji : j ≤ i) : M.indep j := 
exists.elim hi (λ b hb, ⟨b, ⟨hb.1, hji.trans hb.2⟩⟩)

lemma indep.inf_left_indep (hi : M.indep i) (x : α) : M.indep (x ⊓ i) := 
hi.indep_of_le inf_le_right

lemma indep.inf_right_indep (hi : M.indep i) (x : α) : M.indep (i ⊓ x) := 
hi.indep_of_le inf_le_left

lemma bot_indep [order_bot α] (M : supermatroid α): M.indep ⊥ := 
exists.elim M.exists_basis (λ b h, ⟨b, h, bot_le⟩)

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

lemma spanning.super_of (hs : M.spanning s) (hxs : x ≤ s) 
  (h : ∀ t, M.spanning t → x ≤ t → t ≤ s → t = s) : M.super_of s x :=
⟨hs, hxs, h⟩

lemma spanning.spanning_of_le (hs : M.spanning s) (hst : s ≤ t) : M.spanning t := 
exists.elim hs (λ b hb, ⟨b, hb.1, hb.2.trans hst⟩)

lemma spanning.sup_left_spanning (hs : M.spanning s) (x : α) : M.spanning (x ⊔ s) := 
  hs.spanning_of_le le_sup_right

lemma spanning.sup_right_spanning (hs : M.spanning s) (x : α) : M.spanning (s ⊔ x) := 
  hs.spanning_of_le le_sup_left

lemma basis.indep (h : M.basis b) : M.indep b := ⟨b, h, rfl.le⟩ 

lemma exists_indep (M : supermatroid α) : ∃ i, M.indep i := 
exists.elim M.exists_basis (λ b hb, ⟨b, hb.indep⟩)

lemma basis.indep_of_le (hb : M.basis b) (hi : i ≤ b) : M.indep i := ⟨b,hb,hi⟩ 

lemma basis.inf_left_indep (hb : M.basis b) (x : α) : M.indep (x ⊓ b) := 
hb.indep.indep_of_le inf_le_right

lemma basis.inf_right_indep (hb : M.basis b) (x : α) : M.indep (b ⊓ x) := 
hb.indep.indep_of_le inf_le_left

lemma basis.spanning (h : M.basis b) : M.spanning b := ⟨b, h, rfl.le⟩

lemma basis.spanning_of_le (h : M.basis b) (hbs : b ≤ s) : M.spanning s := 
  h.spanning.spanning_of_le hbs 

lemma basis.sup_left_spanning (h : M.basis b) (x : α) : M.spanning (x ⊔ b) := 
  h.spanning.sup_left_spanning _ 

lemma basis.sup_right_spanning (h : M.basis b) (x : α) : M.spanning (b ⊔ x) := 
  h.spanning.sup_right_spanning _ 

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

lemma super_of.spanning (h : M.super_of s x) : M.spanning s := h.1 

lemma super_of.le (h : M.super_of s x) : x ≤ s := h.2.1 

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

lemma super_of.eq_of_spanning_le (hs : M.super_of s x) (hxt : x ≤ t) (hts : t ≤ s) 
  (ht : M.spanning t) : t = s := 
hs.2.2 _ ht hxt hts

lemma super_of.not_spanning_of_lt (hs : M.super_of s x) (hts : t < s) (hxt : x ≤ t):
  ¬ M.spanning t := 
λ h, hts.ne (hs.eq_of_spanning_le hxt hts.le h)

lemma circuit.not_indep (hc : M.circuit c) : ¬ M.indep c := hc.1 

lemma circuit.dep (hc : M.circuit c) : M.dep c := hc.1 

lemma circuit.indep_of_lt (hC : M.circuit c) (hiC : i < c) : M.indep i := 
  by_contra (λ h, (hiC.ne.symm) (hC.2 h hiC.le))

lemma indep.increment (hi : M.indep i) (hi_nb : ¬M.basis i) (hb : M.basis b) : 
  ∃ i', i < i' ∧ i' ≤ i ⊔ b ∧ M.indep i' := 
begin
  obtain ⟨b₁, hb₁, hib₁⟩ := hi, 
  obtain ⟨b₂, hb₂, hib₂, hb₂i⟩ := M.basis_middle i (i ⊔ b) _ hb₁ _ hb le_sup_left hib₁ le_sup_right, 
  exact ⟨b₂, lt_of_le_of_ne' hib₂ (λ h, hi_nb (h ▸ hb₂)), hb₂i, hb₂.indep⟩, 
end 

lemma spanning.decrement (hs : M.spanning s) (hs_nb : ¬M.basis s) (hb : M.basis b) : 
  ∃ t, t < s ∧ s ⊓ b ≤ t ∧ M.spanning t := 
begin
  obtain ⟨b₁, hb₁, hb₁s⟩ := hs, 
  obtain ⟨b₂, hb₂, hb₂s, hsb₂⟩ := M.basis_middle (s ⊓ b) s _ hb _ hb₁ inf_le_left inf_le_right hb₁s,
  refine ⟨b₂, lt_of_le_of_ne hsb₂ (λ h, hs_nb (h ▸ hb₂)), hb₂s, hb₂.spanning⟩, 
end 

lemma basis_of_indep_spanning (hi : M.indep x) (hs : M.spanning x) : M.basis x := 
begin 
  obtain ⟨⟨bi,hbi,hxbi⟩,⟨bs,hbs,hbsx⟩⟩ := ⟨hi,hs⟩, 
  refine by_contra (λ h, (M.basis_antichain hbs hbi (λ h', h _) (hbsx.trans hxbi)).elim), 
  subst h', rwa (hxbi.antisymm hbsx), 
end 

lemma top_spanning [order_top α] (M : supermatroid α) : M.spanning ⊤ := 
exists.elim (M.exists_basis) (λ b hb, ⟨b,hb,le_top⟩)

lemma bases_inj {M₁ M₂ : supermatroid α} (hb : M₁.basis = M₂.basis)  : M₁ = M₂ := by {ext, rw hb}

lemma indep_inj {M₁ M₂ : supermatroid α} (hb : M₁.indep = M₂.indep)  : M₁ = M₂ := 
by {ext, simp_rw [basis_iff_maximal_indep, hb]}

lemma basis_of.basis (hb : M.basis_of b x) (hx : M.spanning x) : M.basis b := 
begin
  by_contradiction h, 
  obtain ⟨b',hb',hxb'⟩ := hx, 
  obtain ⟨j,hjb,hbj,hj⟩ := hb.indep.increment h hb', 
  refine hb.not_indep_of_lt hjb (le_trans hbj (sup_le hb.le hxb')) hj, 
end 

lemma super_of.basis (hs : M.super_of s x) (hx : M.indep x) : M.basis s :=
begin
  by_contradiction h, 
  obtain ⟨b',hb',hxb'⟩ := hx, 
  obtain ⟨t,hts, hst,ht⟩ := hs.spanning.decrement h hb', 
  exact hs.not_spanning_of_lt hts (le_trans (le_inf hs.le hxb') hst) ht, 
end 

end basic 

section infinite_axioms_needed

--maxinf
lemma indep.le_basis_of (hi : M.indep i) (hix : i ≤ x) :
  ∃ j, i ≤ j ∧ M.basis_of j x := 
begin
  obtain ⟨b,hb,hbi⟩ := hi, 
  obtain ⟨b',⟨hb',hb'x,hb'_max⟩⟩ := M.basis_max_inf x _ hb, 
  refine ⟨b' ⊓ x, le_inf ((le_inf hbi hix).trans hb'x) hix, hb'.inf_right_indep _,inf_le_right, _⟩, 
  rintros j ⟨b'',hb'',hjb''⟩ hjx hb'j, 
  have h₀ := (le_inf hjb'' hjx), 
  rw [←(hb'_max _ hb'' (hb'j.trans hjb''))] at h₀, 
  exact le_antisymm hb'j h₀, 
end 

--maxinf
lemma exists_basis_of (M : supermatroid α) (x : α) : ∃ i, M.basis_of i x :=
begin
  obtain ⟨b,hb⟩ := M.exists_basis, 
  obtain ⟨i,-,hi⟩ := (hb.inf_right_indep x).le_basis_of inf_le_right, 
  exact ⟨i,hi⟩, 
end 
--maxinf
lemma indep.le_basis_sup (hi : M.indep i) (hb : M.basis b) : 
   ∃ b', M.basis b' ∧ i ≤ b' ∧ b' ≤ i ⊔ b :=
begin
  obtain ⟨b',hib', hb'⟩ := hi.le_basis_of (@le_sup_left _ _ i b), 
  exact ⟨b',hb'.basis ⟨b,hb,le_sup_right⟩, hib', hb'.le⟩, 
end 

--maxinf
lemma indep.lt_basis_sup (hi : M.indep i) (hi_nb : ¬ M.basis i) (hb : M.basis b) :
  ∃ b', M.basis b' ∧ i < b' ∧ b' ≤ i ⊔ b :=
begin
  obtain ⟨b',hb',h₁,h₂⟩ := hi.le_basis_sup hb, 
  exact ⟨b', hb', lt_of_le_of_ne h₁ (λ h, (hi_nb (h.symm ▸ hb')).elim), h₂⟩, 
end 

--maxinf
lemma basis.inf_basis_of (hb : M.basis b) (x : α) : 
  ∃ b', b' ≤ x ⊔ b ∧ M.basis b' ∧ (M.basis_of (b' ⊓ x) x) :=
begin
  obtain ⟨i,hi⟩ := M.exists_basis_of x, 
  obtain ⟨b',⟨hb',bib',hb'i⟩⟩ := hi.indep.le_basis_sup hb,
  refine ⟨b', hb'i.trans (sup_le_sup_right hi.le _) ,hb', 
    (hb'.inf_right_indep _).basis_of inf_le_right (λ j hj hjx hb'j, hb'j.antisymm (le_inf _ hjx))⟩,
  rwa ←hi.eq_of_le_indep (le_trans (le_inf bib' hi.le) hb'j) hjx hj,  
end 

--maxinf
lemma basis.lt_basis_sup (hb : M.basis b) (hib : i < b) (hb' : M.basis b'):
  ∃ b₀, M.basis b₀ ∧ i < b₀ ∧ b₀ ≤ i ⊔ b' :=
(hb.indep_of_le hib.le).lt_basis_sup (hb.not_basis_of_lt hib) hb' 


-- --minsup
-- lemma spanning.super_of_le (hs : M.spanning s) (hxs : x ≤ s) : 
--   ∃ t, t ≤ s ∧ M.super_of t x :=
-- begin
--   obtain ⟨b,hb,hbs⟩ := hs, 
--   obtain ⟨b',⟨hb',hb'x,hb'_min⟩⟩:= M.basis_min_sup x _ hb, 
--   have hb's : b' ≤ s := hb'x.trans (sup_le hbs hxs), 
--   refine ⟨b' ⊔ x, sup_le hb's hxs, hb'.sup_right_spanning _, le_sup_right, _⟩, 
--   rintros t ⟨b'',hb'',hb''t⟩ hxt htx, 
--   have h₀ := hb'_min _ hb'' (hb''t.trans htx), 
--   rw h₀ at htx ⊢, 
--   exact le_antisymm htx (sup_le hb''t hxt), 
-- end

-- --minsup
-- lemma exists_super_of (M : supermatroid α) (x : α) : 
--   ∃ s, M.super_of s x :=
-- begin
--   obtain ⟨b,hb⟩ := M.exists_basis,
--   obtain ⟨s,-,hs⟩ := (hb.sup_right_spanning x).super_of_le le_sup_right, 
--   exact ⟨s,hs⟩,
-- end 

-- --minsup
-- lemma spanning.basis_inf_le (hs : M.spanning s) (hb : M.basis b) :
--   ∃ b', M.basis b' ∧ b' ≤ s ∧ s ⊓ b ≤ b' := 
-- begin
--   obtain ⟨b₁,hb₁,hb₁s⟩ := hs, 
--   obtain ⟨b',hb',hsb',hb's⟩ := M.basis_middle (s ⊓ b) s _ hb _ hb₁ inf_le_left inf_le_right hb₁s, 
--   refine ⟨b',hb', hb's, hsb'⟩, 
-- end 

-- --minsup
-- lemma spanning.basis_inf_lt (hs : M.spanning s) (hs_nb : ¬ M.basis s) (hb : M.basis b) :
--   ∃ b', M.basis b' ∧ b' < s ∧ s ⊓ b ≤ b' := 
-- begin
--   obtain ⟨b', hb', h₁, h₂⟩ := hs.basis_inf_le hb, 
--   exact ⟨b', hb', lt_of_le_of_ne h₁ (λ h, hs_nb (by rwa ←h)), h₂⟩, 
-- end 

-- --minsup
-- lemma basis.basis_inf_lt (hb : M.basis b) (hbs : b < s) (hb' : M.basis b'): 
--   ∃ b₀, M.basis b₀ ∧ b₀ < s ∧ s ⊓ b' ≤ b₀ := 
-- (hb.spanning_of_le hbs.le).basis_inf_lt (hb.lt_not_basis hbs) hb'

-- --minsup
-- lemma basis.sup_super_of (hb : M.basis b) (x : α) :
--   ∃ b', x ⊓ b ≤ b' ∧ M.basis b' ∧ M.super_of (b' ⊔ x) x  :=
-- begin
--   obtain ⟨s,hs⟩ := M.exists_super_of x, 
--   obtain ⟨b',hb',hsb',hb's⟩ := hs.spanning.basis_inf_le hb, 
--   refine ⟨b', le_trans (le_inf (inf_le_left.trans hs.le) inf_le_right ) hb's, hb', 
--     (hb'.sup_right_spanning _).super_of le_sup_right (λ t ht hxt h, h.antisymm (sup_le _ hxt))⟩, 
--   rwa (hs.eq_of_spanning_le hxt (h.trans (sup_le hsb' hs.le)) ht), 
-- end 




end infinite_axioms_needed

end supermatroid 