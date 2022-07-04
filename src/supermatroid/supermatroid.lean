/-
Copyright stuff
-/
import .base_family

/-! 
This file defines `supermatroids`; these are nonempty antichains of `bases` in a modular lattice 
that satisfy two axioms asserting the existence of bases under various conditions.
-/

universes u v 

variables {α : Type u} {κ : Type v}

open set order_dual 

/-- In a matroid on a finite lattice, bases for sets exist -/
lemma indep.le_basis_of_le_of_finite [base_family α] [finite α] {i x : α} (hi : indep i) 
(hix : i ≤ x) : 
  ∃ j, j basis_for x ∧ i ≤ j := 
(set.finite.exists_maximal_mem 
  (⟨i, ⟨hi,rfl.le,hix⟩⟩ : {i' | indep i' ∧ i ≤ i' ∧ i' ≤ x}.nonempty)).imp 
    (λ j ⟨⟨hj, hij,hjx⟩,hj_max⟩, 
     ⟨⟨hj,hjx, λ j' hj' hj'x hjj', hj_max j' ⟨hj',hij.trans hjj',hj'x⟩ hjj'⟩, hij⟩)

/-- In a matroid on a finite lattice, canopies for sets exist -/
lemma spanning.super_of_le_of_le_of_finite [base_family α] [finite α] {s x : α} (hs : spanning s)
(hxs : x ≤ s) :
  ∃ t, t canopy_for x ∧ t ≤ s := 
@indep.le_basis_of_le_of_finite αᵒᵈ _ _ _ _ hs hxs

section supermatroid 

/-- Class for base families that satisfy an augmentation axiom and in which the base lattice
is modular. Equivalent to independence augmentation in the case of finite set lattices. -/
class supermatroid (α : Type u) extends base_family α, is_modular_lattice α :=
(exists_base_mid_of_indep_le_spanning : 
  ∀ (x y : α), indep x → spanning y → x ≤ y → ∃ b, base b ∧ x ≤ b ∧ b ≤ y) 
(le_basis_of_indep_le : ∀ (i x : α), indep i → i ≤ x → ∃ j, j basis_for x ∧ i ≤ j)
  
variables [supermatroid α] {a i j b b' s t x y z x' y' z' : α}

/-- A base_family on a finite lattice that satisfies the middle axiom is a supermatroid. -/
noncomputable lemma supermatroid_of_finite {α : Type u} [base_family α] [finite α] 
[is_modular_lattice α] 
(h : ∀ (x y : α), indep x → spanning y → x ≤ y → ∃ b, base b ∧ x ≤ b ∧ b ≤ y) : 
  supermatroid α :=
⟨h, @indep.le_basis_of_le_of_finite _ _ _⟩ 

/-- #### Extensions to bases -/

lemma indep.exists_base_mid_of_le_spanning (hi : indep i) (hs : spanning s) (his : i ≤ s) : 
  ∃ b, base b ∧ i ≤ b ∧ b ≤ s := 
supermatroid.exists_base_mid_of_indep_le_spanning _ _ hi hs his  

lemma indep.exists_base_mid_of_le_sup_base (hi : indep i) (hb : base b) : 
   ∃ b', base b' ∧ i ≤ b' ∧ b' ≤ i ⊔ b :=
hi.exists_base_mid_of_le_spanning (hb.sup_left_spanning _) le_sup_left

lemma base.exists_base_of_subset_le_supset_base (hb : base b) (hb' : base b') (hxy : x ≤ y) 
  (hxb : x ≤ b) (hb'y : b' ≤ y): 
   ∃ b₀, base b₀ ∧ x ≤ b₀ ∧ b₀ ≤ y :=
supermatroid.exists_base_mid_of_indep_le_spanning _ _ ⟨b,hb,hxb⟩ ⟨b',hb',hb'y⟩ hxy 

lemma indep.lt_base_le_spanning_of_not_base (hi : indep i) (hi_b : ¬base i) (hs : spanning s)
(his : i ≤ s) :
  ∃ b, base b ∧ i < b ∧ b ≤ s  := 
(hi.exists_base_mid_of_le_spanning hs his).imp 
  (λ j, λ ⟨hj,hij,hjs⟩, ⟨hj, hij.lt_of_ne (λ h, hi_b (h.substr hj)), hjs⟩)

lemma indep.lt_base_sup_le_sup_base_of_not_base (hi : indep i) (hi_nb : ¬ base i) 
(hb : base b) :
  ∃ b', base b' ∧ i < b' ∧ b' ≤ i ⊔ b :=
(hi.lt_base_le_spanning_of_not_base hi_nb (hb.sup_left_spanning _) le_sup_left)

lemma indep.lt_base_le_spanning_of_lt (hj : indep j) (hs : spanning s) (hi : i < j) (his : i ≤ s) :
  ∃ b, base b ∧ i < b ∧ b ≤ s :=
(hj.indep_of_le hi.le).lt_base_le_spanning_of_not_base (hj.not_base_of_lt hi) hs his

lemma indep.lt_base_le_sup_base_of_lt (hj : indep j) (hi : i < j) (hb : base b) :
  ∃ b', base b' ∧ i < b' ∧ b' ≤ i ⊔ b :=
hj.lt_base_le_spanning_of_lt (hb.sup_left_spanning _) hi le_sup_left

lemma indep.base_of_spanning (hi : indep i) (hs : spanning i) : base i := 
exists.elim (hi.exists_base_mid_of_le_spanning hs rfl.le) 
  (λ a ⟨ha,hia,hai⟩, (hai.antisymm hia).subst ha)

lemma indep.le_basis_of_le (hi : indep i) (hix : i ≤ x) : ∃ j, j basis_for x ∧ i ≤ j := 
supermatroid.le_basis_of_indep_le _ _ hi hix  

lemma indep.le_basis_sup_right (hi : indep i) (x : α) : ∃ j, j basis_for (i ⊔ x) ∧ i ≤ j := 
hi.le_basis_of_le le_sup_left 

lemma indep.le_basis_sup_left (hi : indep i) (x : α) : ∃ j, j basis_for (x ⊔ i) ∧ i ≤ j := 
hi.le_basis_of_le le_sup_right 

lemma indep.lt_basis_of_not_basis_of_le (hi : indep i) (hi_n : ¬ i basis_for x) 
(hix : i ≤ x) : 
  ∃ j, j basis_for x ∧ i < j := 
(hi.le_basis_of_le hix).imp (λ j hj, ⟨hj.1, hj.2.lt_of_ne (λ h, hi_n (h.substr hj.1))⟩) 

lemma indep.exists_lt_inf_base_of_not_basis (hi : indep i) (hnb : ¬ i basis_for x) 
(hix : i ≤ x) : 
  ∃ b, base b ∧ (x ⊓ b) basis_for x ∧ i < x ⊓ b := 
begin
  obtain ⟨j,hj,hjx⟩ := hi.lt_basis_of_not_basis_of_le hnb hix, 
  obtain ⟨b,hb,hjb⟩ := hj.indep, 
  refine ⟨b, hb, (hb.inf_left_indep _).basis_for inf_le_left _, hjx.trans_le (le_inf hj.le hjb)⟩, 
  refine λ j' hj' hj'x hbxj, hbxj.antisymm _, 
  rw ←hj.eq_of_le_indep hj' ((le_inf hj.le hjb).trans hbxj) hj'x, 
  exact le_inf hj.le hjb, 
end 

lemma basis_for.base (hb : b basis_for s) (hs : spanning s) : base b := 
exists.elim (hb.indep.exists_base_mid_of_le_spanning hs hb.le) 
  (λ b' ⟨hb',hbb',hb's⟩, (hb.eq_of_le_indep hb'.indep hbb' hb's).substr hb') 

lemma exists_basis (x : α) : ∃ i, i basis_for x := 
exists.elim (exists_base α) 
  (λ b hb, ((hb.inf_right_indep x).le_basis_of_le inf_le_right).imp (λ _ h, h.1)) 

lemma base.inf_basis (hb : base b) (x : α) : 
  ∃ b', base b' ∧ ((b' ⊓ x) basis_for x) ∧ b' ≤ x ⊔ b  :=
begin
  obtain ⟨i,hi⟩ := exists_basis x, 
  obtain ⟨b',⟨hb',bib',hb'i⟩⟩ := hi.indep.exists_base_mid_of_le_sup_base hb,
  refine ⟨b',hb', 
    (hb'.inf_right_indep _).basis_for inf_le_right (λ j hj hjx hb'j, hb'j.antisymm (le_inf _ hjx)), 
    hb'i.trans (sup_le_sup_right hi.le _)⟩,
  rwa ←hi.eq_of_le_indep hj (le_trans (le_inf bib' hi.le) hb'j) hjx,  
end 

lemma base.lt_base_le_spanning_of_lt (hb : base b) (hs : spanning s) (hib : i < b) 
(his : i ≤ s) :
  ∃ b₀, base b₀ ∧ i < b₀ ∧ b₀ ≤ s := 
(hb.indep_of_le hib.le).lt_base_le_spanning_of_not_base (hb.not_base_of_lt hib) hs his 

lemma base.lt_base_le_sup_base_of_lt (hb : base b) (hb' : base b') (hib : i < b) :
  ∃ b₀, base b₀ ∧ i < b₀ ∧ b₀ ≤ i ⊔ b' :=
(hb.indep_of_le hib.le).lt_base_sup_le_sup_base_of_not_base (hb.not_base_of_lt hib) hb' 
 
/-- #### Duality -/

private lemma spanning.canopy_le_of_le' (hs : spanning s) (hxs : x ≤ s) : 
  ∃ t, t canopy_for x ∧ t ≤ s :=
begin
  obtain ⟨b,hb,hbs⟩ := hs, 
  obtain ⟨b₁, hb₁, hb₁x, hb₁b⟩ := hb.inf_basis x, 
  refine ⟨x ⊔ b₁, ⟨hb₁.sup_left_spanning _, le_sup_left, _⟩, 
    sup_le hxs (hb₁b.trans (sup_le hxs hbs))⟩, 
  rintros t ⟨b₂,hb₂,hb₂t⟩ hxt hty,
  refine (sup_le hxt (by_contra (λ hb₁t, _))).antisymm hty,   
  set j := b₁ ⊓ (x ⊔ b₂) with hj, 

  have hj_lt : j < b₁ := inf_le_left.lt_of_ne 
    (λ h_eq, hb₁t (by {rw ← h_eq, exact inf_le_right.trans (sup_le hxt hb₂t)})),   
  
  obtain ⟨b₃, hb₃, hjb₃, hb₃j⟩ := hb₁.lt_base_le_sup_base_of_lt hb₂ hj_lt, 

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

/-- A supermatroid family is also a supermatroid family in the dual  -/
instance : supermatroid αᵒᵈ := 
⟨ λ i s hi hs his, 
  (indep.exists_base_mid_of_le_spanning hs hi his).imp (λ b ⟨hb,hsb,hbi⟩, ⟨hb, hbi, hsb⟩), 
  λ i x hi hix, (spanning.canopy_le_of_le' hi hix).imp (λ a ⟨ha, hia⟩, ⟨ha, hia⟩)⟩

lemma exists_canopy (x : α) : ∃ s, s canopy_for x := @exists_basis αᵒᵈ _ x

/-- #### Spanning sets -/

-- Need to rename the lemmas in this section to match their indep equivalents 

lemma spanning.exists_base_mid_of_indep_le (hs : spanning s) (hi : indep i) (his : i ≤ s) :
  ∃ b, base b ∧ b ≤ s ∧ i ≤ b :=
@indep.exists_base_mid_of_le_spanning αᵒᵈ _ _ _ hs hi his  

lemma spanning.base_lt_indep_le_of_not_base (hs : spanning s) (hs_nb : ¬base s) (hi : indep i) 
(his : i ≤ s) : 
  ∃ b, base b ∧ b < s ∧ i ≤ b := 
@indep.lt_base_le_spanning_of_not_base αᵒᵈ _ _ _ hs hs_nb hi his

lemma spanning.base_lt_inf_base_le_of_not_base (hs : spanning s) (hs_nb : ¬base s)
(hb : base b) : 
  ∃ b', base b' ∧ b' < s ∧ s ⊓ b ≤ b' := 
@indep.lt_base_sup_le_sup_base_of_not_base αᵒᵈ _ _ _ hs hs_nb hb 

lemma canopy_for.base (hs : s canopy_for x) (hx : indep x) : base s :=
@basis_for.base αᵒᵈ _ _ _ hs hx

lemma spanning.canopy_le_of_le (hs : spanning s) (hxs : x ≤ s) : ∃ t, t canopy_for x ∧ t ≤ s :=
spanning.canopy_le_of_le' hs hxs

lemma spanning.base_le_base_inf_le (hs : spanning s) (hb : base b) :
  ∃ b', base b' ∧ b' ≤ s ∧ s ⊓ b ≤ b' := 
@indep.exists_base_mid_of_le_sup_base αᵒᵈ _ _ _ hs hb 

lemma spanning.exists_sup_base_lt_of_not_canopy_for (hs : spanning s) (hnb : ¬ s canopy_for x) 
(hix : x ≤ s) : 
  ∃ b, base b ∧ (x ⊔ b) canopy_for x ∧ x ⊔ b < s := 
@indep.exists_lt_inf_base_of_not_basis αᵒᵈ _ _ _ hs hnb hix

lemma base.base_lt_inf_le_base_of_lt (hb : base b) (hb' : base b') (hbs : b < s) : 
  ∃ b₀, base b₀ ∧ b₀ < s ∧ s ⊓ b' ≤ b₀ := 
@base.lt_base_le_sup_base_of_lt αᵒᵈ _ _ _ _ hb hb' hbs 

lemma base.sup_canopy_for (hb : base b) (x : α) :
  ∃ b',base b' ∧ (b' ⊔ x) canopy_for x ∧ x ⊓ b ≤ b'  :=
@base.inf_basis αᵒᵈ _ _ hb x

lemma basis_for.eq_inf_base_of_le_base (hix : i basis_for x) (hb : base b) (hib : i ≤ b) : 
  i = x ⊓ b := 
hix.eq_of_le_indep (hb.inf_left_indep x) (le_inf hix.le hib) inf_le_left 

lemma basis_for.exists_base (hi : i basis_for x) : 
  ∃ b, base b ∧ i = x ⊓ b ∧ ∀ b', base b' → x ⊓ b ≤ b' → x ⊓ b' = x ⊓ b := 
begin
  obtain ⟨b, hb, hib⟩ := hi.indep, 
  have := hi.eq_inf_base_of_le_base hb hib, subst this, 
  exact ⟨_,hb, rfl, λ b' hb' hxb', 
    (hi.eq_of_le_indep (hb'.inf_left_indep x) (le_inf inf_le_left hxb') inf_le_left).symm⟩, 
end 

lemma basis_for.eq_inf_base_both (hix : i basis_for x) (hiy : i basis_for y) : 
  ∃ b, base b ∧ i = x ⊓ b ∧ i = y ⊓ b :=
hix.indep.imp (λ b hb, ⟨hb.1, hix.eq_inf_base_of_le_base hb.1 hb.2, 
    hiy.eq_inf_base_of_le_base hb.1 hb.2⟩)

lemma canopy_for.eq_sup_super_both (hsx : s canopy_for x) (hsy : s canopy_for y) : 
  ∃ b, base b ∧ s = x ⊔ b ∧ s = y ⊔ b :=
@basis_for.eq_inf_base_both αᵒᵈ _ _ _ _ hsx hsy

lemma eq_inf_basisall_of_basisall {x : κ → α} (h : ∀ k, i basis_for x k) : 
  ∃ b, base b ∧ ∀ k, i = (x k) ⊓ b := 
(is_empty_or_nonempty κ).elim (λ he, (exists_base α).imp (λ b hb, ⟨hb, he.elim⟩ )) 
  (λ ⟨k⟩, (h k).indep.imp (λ b hb, ⟨hb.1, λ k', (h k').eq_inf_base_of_le_base hb.1 hb.2⟩))

lemma eq_inf_basisall_of_basisall_mem {S : set α} (hS : ∀ x ∈ S, i basis_for x) :
  ∃ b, base b ∧ ∀ x ∈ S, i = x ⊓ b :=
(@eq_inf_basisall_of_basisall α S _ i coe (λ ⟨x,hx⟩, hS x hx)).imp 
  (λ b hb, ⟨hb.1, λ x hx, (hb.2 ⟨x,hx⟩)⟩)

lemma eq_sup_basisall_of_canopy_forall {x : κ → α} (h : ∀ k, s canopy_for x k) :
  ∃ b, base b ∧ ∀ k, s = x k ⊔ b :=
@eq_inf_basisall_of_basisall αᵒᵈ κ _ _ _ h

lemma eq_sup_basisall_of_canopy_forall_mem {S : set α} (hS : ∀ x ∈ S, s canopy_for x) : 
  ∃ b, base b ∧ ∀ x ∈ S, s = x ⊔ b :=
@eq_inf_basisall_of_basisall_mem αᵒᵈ _ _ S hS


lemma canopy_for.eq_sup_base_both (hsx : s canopy_for x) (hsy : s canopy_for y) : 
  ∃ b, base b ∧ s = x ⊔ b ∧ s = y ⊔ b := 
@basis_for.eq_inf_base_both αᵒᵈ _ _ _ _ hsx hsy 

-- Probably this lemma is the right way to do duality. It might be that only semimodularity is needed... 

lemma base.sup_canopy_of_inf_basis (hb : base b) (hbx : (x ⊓ b) basis_for x) : 
  (x ⊔ b) canopy_for x :=
begin
  by_contradiction h,
  obtain ⟨b₁,hb₁,-, hb₁x⟩ := 
    (hb.sup_left_spanning x).exists_sup_base_lt_of_not_canopy_for h le_sup_left, 
  
  set i := (x ⊔ b₁) ⊓ b with hi, 

  have hlt : i < b := lt_of_le_of_ne inf_le_right 
    (λ h, hb₁x.ne (le_antisymm 
      (sup_le (le_sup_left.trans hb₁x.le) (le_sup_right.trans hb₁x.le)) 
      (sup_le (le_sup_left) (by {rw [←h,hi], exact inf_le_left})))), 
  
  obtain ⟨b₂,hb₂,hib₂,hb₂i⟩ := hb.lt_base_le_sup_base_of_lt hb₁ hlt, 
  
  have hlast := @inf_lt_inf_of_lt_of_sup_le_sup _ _ _ _ _ x hib₂ (sup_le _ le_sup_right),
  { refine hbx.not_indep_of_lt (lt_of_le_of_lt _ hlast) inf_le_right (hb₂.inf_right_indep x),  
    exact le_inf (le_inf (inf_le_left.trans le_sup_left) inf_le_right) inf_le_left},
  rw [hi, inf_sup_assoc_of_le, le_inf_iff] at hb₂i ⊢, 
  { exact ⟨hb₂i.1, hb₂i.1.trans (hb₁x.le.trans_eq sup_comm)⟩},
  exact le_sup_left, exact le_sup_right,
end 

lemma base.sup_canopy_iff_inf_basis (hb : base b):
  (x ⊔ b) canopy_for x ↔ (x ⊓ b) basis_for x := 
⟨@base.sup_canopy_of_inf_basis αᵒᵈ _ _ _ hb, hb.sup_canopy_of_inf_basis⟩

-- This lemma is the independence augmentation axiom in the restriction to `x`
lemma indep.lt_basis_le_sup_of_not_basis (hi : indep i) (hin : ¬ (i basis_for x)) 
(hj : j basis_for x) (hix : i ≤ x) :
  ∃ i', i' basis_for x ∧ i < i' ∧ i' ≤ i ⊔ j :=
begin
  obtain ⟨b₁, hb₁, rfl, -⟩ := hj.exists_base, 
  obtain ⟨b₂, hb₂,hib₂, hb₂i⟩ := hi.exists_base_mid_of_le_sup_base hb₁, 
  rw [←hb₁.sup_canopy_iff_inf_basis] at hj,
  have hb₁b₂ := hj.eq_of_spanning_le (hb₂.sup_left_spanning x) le_sup_left
    (sup_le le_sup_left (hb₂i.trans (sup_le (le_sup_of_le_left hix) le_sup_right))),
  rw [←hb₁b₂, hb₂.sup_canopy_iff_inf_basis] at hj, 
  refine ⟨x ⊓ b₂, hj, (le_inf hix hib₂).lt_of_ne (λ h, hin (by rwa ←h at hj)),
    (inf_le_inf_left x hb₂i).trans _⟩, 
  rw [inf_comm, sup_inf_assoc_of_le _ hix, inf_comm], 
end 

/-- This lemma is saying that `x ⊔ i` is a canopy for `x` in the restriction to `x ⊔ i` --/
lemma sup_eq_of_basis_basis_basis (hi_inf : x ⊓ i basis_for x) (hi_sup : i basis_for x ⊔ i) 
(hj : j basis_for x ⊔ i) : 
  x ⊔ j = x ⊔ i :=
begin
  refine (sup_le le_sup_left hj.le).antisymm (sup_le le_sup_left (by_contra (λ h', _))), 
  
  have hnb : ¬ (i ⊓ (x ⊔ j)) basis_for x ⊔ i := hi_sup.not_basis_of_lt (inf_le_left.lt_of_ne
    (λ h_eq, by {rw ←h_eq at h', exact h' inf_le_right} )),

  obtain ⟨i₁, hi₁,hi'i₁,hi₁i'⟩ := (hi_sup.indep.inf_right_indep _).lt_basis_le_sup_of_not_basis 
    hnb hj (le_sup_of_le_right inf_le_left), 

  have hlt := @inf_lt_inf_of_lt_of_sup_le_sup _ _ _ _ _ x hi'i₁
    (sup_le (hi₁i'.trans (sup_le le_sup_left 
      (by {rw [inf_comm, inf_sup_assoc_of_le _ (le_sup_left : x ≤ x ⊔ j), @sup_comm _ _ i], 
          exact le_inf le_sup_right hj.le}))) le_sup_right), 

  rw [inf_assoc, @inf_comm _ _ _ x, inf_sup_self, inf_comm, @inf_comm _ _ i₁] at hlt, 
  exact hi_inf.not_indep_of_lt hlt inf_le_left (hi₁.indep.inf_left_indep _), 
end 

lemma basis_for.basis_sup_mono (hix : i basis_for x) (hj : indep j) (hij : i ≤ j) :
  j basis_for (x ⊔ j) :=
begin
  obtain ⟨b, hb, hjb⟩ := hj, 
  obtain ⟨j',hj',hjj'⟩ := (hb.indep_of_le hjb).le_basis_of_le (le_sup_right : j ≤ x ⊔ j), 
  obtain rfl := 
    (hix.eq_of_le_indep (hb.inf_left_indep x) (le_inf hix.le (hij.trans hjb)) inf_le_left), 
  by_contra h, 
  have hlt  := hjj'.lt_of_ne (by {rintro rfl, exact h hj'}),

  refine hix.not_indep_of_lt _ inf_le_right (hj'.indep.inf_right_indep x),
  refine lt_of_le_of_lt (le_inf hij inf_le_left) 
    (inf_lt_inf_of_lt_of_sup_le_sup hlt (sup_le (sup_comm.subst hj'.le) le_sup_right)),
end 

lemma canopy_for.canopy_inf_mono (hsx : s canopy_for x) (ht : spanning t) (hts : t ≤ s) :
  t canopy_for (x ⊓ t) :=
@basis_for.basis_sup_mono αᵒᵈ _ _ _ _ hsx ht hts

end supermatroid
