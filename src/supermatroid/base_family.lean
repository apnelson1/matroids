/- Blah copyright
-/
import .easy_lemmas 
import order.minimal 
import order.hom.complete_lattice

/-! 
This file defines a `base_family`, which is simply a nonempty antichain in a complete lattice, 
and a host of matroidal terminology such as independent/dependent elements, spanning elements, 
circuits, hyperplanes, bases and canopies for elements, etc. None of the material here uses 
any nontrivial 'augmentation'-type axioms. First PR? 
-/

universes u v 

variables {α : Type u}

open set order_dual 

section base_family 

/-- A `base_family` is a nonempty antichain in a complete lattice -/
class base_family (α : Type u) extends complete_lattice α := 
(carrier : set α)
(nonempty : carrier.nonempty)
(is_antichain : is_antichain (≤) carrier)

/-- A `base_family` is also a base family in the dual order -/
instance {α : Type u} [base_family α]: base_family αᵒᵈ := { 
carrier := of_dual ⁻¹' base_family.carrier,
nonempty := base_family.nonempty,
is_antichain := base_family.is_antichain.to_dual }


variables [base_family α] {x y z x' y' z'  i j a b b' c s t f d : α}

/-! #### Definitions / Existence -/ 
  
def base (x : α) : Prop := x ∈ (base_family.carrier : set α) 

lemma exists_base (α : Type u) [base_family α] : ∃ (b : α), base b := base_family.nonempty

lemma base_antichain : is_antichain (≤) (base : set α) := base_family.is_antichain 

/-- An element below a base is independent-/
def indep (x : α) := ∃ b, base b ∧ x ≤ b 

/-- An element above a base is spanning-/
def spanning (x : α) :=  ∃ b, base b ∧ b ≤ x 

/-- An element that is not independent is depedent-/
@[reducible] def dep (x : α) := ¬ indep x 

-- `x` is loopy if it is 'disjoint' from every base 
--def loopy (x : α) := ∀ b, base b → x ⊓ b = ⊥ 

lemma mem_lower_set_base_iff_indep : indep i ↔ i ∈ lower_closure (base : set α) := 
⟨λ ⟨b,hb,hbx⟩, ⟨b,hb,hbx⟩, λ ⟨b,hb,hbx⟩, ⟨b,hb,hbx⟩⟩

lemma indep.not_dep (hi : indep i) : ¬ dep i := by rwa [not_not]

lemma dep.not_indep (hx : dep x) : ¬ indep x := hx 

lemma not_dep_iff_indep : ¬ dep i ↔ indep i  := by rw [not_not]
  
lemma indep_or_dep (i : α) : indep i ∨ dep i := em _  

lemma not_indep_iff_dep : ¬ indep i ↔ dep i := iff.rfl 

lemma exists_indep : ∃ (i : α), indep i := (exists_base α).imp (λ b hb, ⟨b,hb,rfl.le⟩)

lemma base.indep (h : base b) : indep b := ⟨b, h, rfl.le⟩ 

@[simp] lemma mem_upper_set_base_iff_spanning : s ∈ upper_closure (base : set α) ↔ spanning s := 
⟨λ ⟨b,hb,hbx⟩, ⟨b,hb,hbx⟩, λ ⟨b,hb,hbx⟩, ⟨b,hb,hbx⟩⟩

lemma spanning.spanning_of_le (hs : spanning s) (hst : s ≤ t) : spanning t := 
exists.elim hs (λ b hb, ⟨b, hb.1, hb.2.trans hst⟩)

lemma spanning.sup_right_spanning (hs : spanning s) (x : α) : spanning (s ⊔ x) := 
hs.spanning_of_le le_sup_left 

lemma spanning.sup_left_spanning (hs : spanning s) (x : α) : spanning (x ⊔ s) := 
hs.spanning_of_le le_sup_right

lemma base.spanning (h : base b) : spanning b := ⟨b, h, rfl.le⟩ 

lemma base.spanning_of_le (h : base b) (hbs : b ≤ s) : spanning s := 
h.spanning.spanning_of_le hbs 

-- NB : avoid this one - prefer `x ⊔ b` over `b ⊔ x`
lemma base.sup_right_spanning (hb : base b) (x : α) : spanning (b ⊔ x) := 
hb.spanning.sup_right_spanning _ 

lemma base.sup_left_spanning (hb : base b) (x : α) : spanning (x ⊔ b) := 
hb.spanning.sup_left_spanning _

lemma indep.indep_of_le (hi : indep i) (hji : j ≤ i) : indep j := 
exists.elim hi (λ b hb, ⟨b, ⟨hb.1, hji.trans hb.2⟩⟩)

lemma indep.inf_left_indep (hi : indep i) (x : α) : indep (x ⊓ i) := 
hi.indep_of_le inf_le_right

-- NB : avoid this one - prefer `x ⊓ i` over `i ⊓ x`
lemma indep.inf_right_indep (hi : indep i) (x : α) : indep (i ⊓ x) := 
hi.indep_of_le inf_le_left

lemma bot_indep (α : Type u) [base_family α] : indep (⊥ : α) := 
exists.elim (exists_base α) (λ b h, ⟨b, h, bot_le⟩)

lemma dep.dep_of_lt (hx : dep x) (hxy : x ≤ y) : dep y := 
not_indep_iff_dep.mp (λ h, (hx.not_indep (h.indep_of_le hxy)).elim)

lemma base.indep_of_le (hb : base b) (hi : i ≤ b) : indep i := ⟨b,hb,hi⟩ 

lemma base.inf_left_indep (hb : base b) (x : α) : indep (x ⊓ b) := 
hb.indep.indep_of_le inf_le_right

-- NB : avoid this one - prefer `x ⊓ b` over `b ⊓ x`
lemma base.inf_right_indep (hb : base b) (x : α) : indep (b ⊓ x) := 
hb.indep.indep_of_le inf_le_left

lemma top_spanning (α : Type u) [base_family α] : spanning (⊤ : α) := 
exists.elim (exists_base α) (λ b hb, ⟨b,hb,le_top⟩) 

lemma indep.base (hi : indep i) (hmax : ∀ j, indep j → i ≤ j → i = j) : base i := 
exists.elim hi (λ b ⟨hb, hbi⟩, (hmax b hb.indep hbi).substr hb)

lemma base.eq_of_le_base (hb : base b) (hx : base x) (hxb : b ≤ x) : b = x :=
by_contra (λ hne, base_antichain hb hx hne hxb)

lemma base.eq_of_le_indep (hb : base b) (hi : indep i) (hbi : b ≤ i) : b = i := 
hbi.antisymm (exists.elim hi (λ b' ⟨hb',hib'⟩,(hb.eq_of_le_base hb' (hbi.trans hib')).substr hib'))

lemma base.eq_of_spanning_le (hb : base b) (hs : spanning s) (hsb : s ≤ b) : s = b :=
hsb.antisymm (exists.elim hs (λ b' ⟨hb',hb's⟩, (hb'.eq_of_le_base hb (hb's.trans hsb)).subst hb's))

lemma base.lt_not_indep (hb : base b) (hbx : b < x) : ¬ indep x := 
λ hx, hbx.ne (hb.eq_of_le_indep hx hbx.le)

lemma base.lt_not_base (hb : base b) (hbx : b < x) : ¬ base x := 
λ h, hb.lt_not_indep hbx h.indep 

lemma base.not_base_of_lt (hb : base b) (hxb : x < b) : ¬ base x := 
λ hx, (hx.lt_not_base hxb) hb  

lemma indep.not_base_of_lt (hi : indep i) (hxi : x < i) : ¬ base x :=
λ hb, hb.lt_not_indep hxi hi 

lemma spanning.eq_of_le_base (hs : spanning s) (hb : base b) (hsb : s ≤ b) : s = b :=
hb.eq_of_spanning_le hs hsb 

lemma base_iff_maximal_indep : base b ↔ (maximals (≤) indep) b := 
⟨λ hb, ⟨hb.indep,λ i hi hbi, hb.eq_of_le_indep hi hbi⟩, 
  λ ⟨⟨b',hb',hbb'⟩, hb''⟩, (hb'' hb'.indep hbb').substr hb'⟩

lemma base_iff_minimal_spanning : base b ↔ b ∈ (minimals (≤) (spanning : set α)) :=
⟨λ hb, ⟨hb.spanning,λ s hs hbs, (hb.eq_of_spanning_le hs hbs).symm⟩, 
  λ ⟨⟨b',hb',hbb'⟩, hb''⟩, (hb'' hb'.spanning hbb').substr hb'⟩

section basis

/-- A basis for `x` is a maximal element that is independent and below `x` -/
def basis_for (i x : α) := indep i ∧ i ≤ x ∧ ∀ j, indep j → j ≤ x → i ≤ j → i = j 

infix ` basis_for `:50 := basis_for

lemma basis_for.indep (h : b basis_for x) : indep b := h.1

lemma basis_for.le (h : b basis_for x) : b ≤ x := h.2.1

lemma indep.basis_for (hi : indep i) (hix : i ≤ x) (h : ∀ j, indep j → j ≤ x → i ≤ j → i = j) : 
  i basis_for x :=
⟨hi,  hix, h⟩

lemma indep.basis_for_self (hi : indep i) : i basis_for i := 
hi.basis_for rfl.le (λ h hj, flip le_antisymm)

lemma base.basis_for_sup_left (hb : base b) (x : α) : b basis_for (b ⊔ x) := 
hb.indep.basis_for le_sup_left (λ j hj hjx hbj, hb.eq_of_le_indep hj hbj)

lemma base.basis_for_sup_right (hb : base b) (x : α) : b basis_for (x ⊔ b) := 
by {rw sup_comm, exact hb.basis_for_sup_left x}

lemma basis_for.eq_of_le_indep (h : b basis_for x) (hy : indep y) (hby : b ≤ y) (hyx : y ≤ x) : 
  b = y := (h.2.2 _ hy hyx hby)

lemma basis_for.not_indep_of_lt (hb : b basis_for x) (hby : b < y) (hyx : y ≤ x) : ¬ indep y := 
λ h, hby.ne (hb.eq_of_le_indep h hby.le hyx)

lemma basis_for.basis_for_of_le (hi : i basis_for x) (hiy : i ≤ y) (hyx : y ≤ x) : i basis_for y := 
hi.indep.basis_for hiy (λ j hj hjy hij, hi.eq_of_le_indep hj hij (hjy.trans hyx))

lemma basis_for.basis_for_sup_of_le (hi : i basis_for x) (hyx : y ≤ x) : i basis_for (i ⊔ y) := 
hi.basis_for_of_le le_sup_left (sup_le hi.le hyx)

lemma basis_for.indep_of_le (hb : b basis_for x) (hib : i ≤ b)  : indep i := 
(hb.indep).indep_of_le hib 

lemma base.basis_for_top (hb : base b) : b basis_for ⊤ := 
hb.indep.basis_for le_top (λ j hj hbj h, hb.eq_of_le_indep hj h) 

lemma basis_for_top_iff : b basis_for ⊤ ↔ base b := 
⟨λ h, h.indep.base (λ j hj hbj, h.eq_of_le_indep hj hbj le_top), base.basis_for_top⟩

lemma basis_for_bot_iff : x basis_for ⊥ ↔ x = ⊥ :=
⟨λ h, le_bot_iff.mp h.le, by {rintro rfl, exact (bot_indep α).basis_for_self}⟩ 

lemma basis_for.basis_for_sup_self (hi : i basis_for x) : i basis_for (x ⊔ i) := 
hi.indep.basis_for le_sup_right 
  (λ j hj hjix hij, (hi.eq_of_le_indep hj hij (by {rwa [sup_eq_left.mpr hi.le] at hjix})))

lemma indep.eq_of_basis_for (hi : indep i) (hj : j basis_for i) : i = j :=
(hj.eq_of_le_indep hi hj.le rfl.le).symm

end basis

section canopy 

/-- A canopy for `x` is a minimal element that is spanning and above `x` -/
def canopy_for (s x : α) := spanning s ∧ x ≤ s ∧ ∀ t, spanning t → x ≤ t → t ≤ s → s = t

infix ` canopy_for `:50 := canopy_for

lemma spanning.canopy_for (hs : spanning s) (hxs : x ≤ s) 
  (h : ∀ t, spanning t → x ≤ t → t ≤ s → s = t) : s canopy_for x :=
⟨hs, hxs, h⟩

lemma canopy_for_iff : 
  s canopy_for x ↔ spanning s ∧ x ≤ s ∧ ∀ s', spanning s' → x ≤ s' → s' ≤ s → s = s' := iff.rfl 

lemma canopy_for.spanning (h : s canopy_for x) : spanning s := h.1 

lemma canopy_for.le (h : s canopy_for x) : x ≤ s := h.2.1 

lemma canopy_for.eq_of_spanning_le (hs : s canopy_for x) (hxt : x ≤ t) (hts : t ≤ s) 
  (ht : spanning t) : t = s := (hs.2.2 _ ht hxt hts).symm

lemma canopy_for.not_spanning_of_lt (hs : s canopy_for x) (hts : t < s) (hxt : x ≤ t):
  ¬ spanning t := 
λ h, hts.ne (hs.eq_of_spanning_le hxt hts.le h)

lemma canopy_for.canopy_for_of_le (hs : s canopy_for x) (hys : y ≤ s) (hxy : x ≤ y) : 
  s canopy_for y := 
@basis_for.basis_for_of_le αᵒᵈ _ _ _ _ hs hys hxy

lemma canopy_for_top_iff : x canopy_for ⊤ ↔ x = ⊤ :=
@basis_for_bot_iff αᵒᵈ _ _

lemma canopy_for_bot_iff : b canopy_for ⊥ ↔ base b := 
@basis_for_top_iff αᵒᵈ _ _

end canopy

section dual 

lemma indep.spanning_dual (hi : indep i) : spanning (to_dual i) := hi 

@[simp] lemma spanning_dual_iff_indep : spanning (to_dual i) ↔ indep i := iff.rfl 

lemma spanning.indep_dual (hs : spanning s) : indep (to_dual s) := hs

@[simp] lemma indep_dual_iff_spanning : indep (to_dual s) ↔ spanning s := iff.rfl 

lemma base.to_dual (hb : base b) : base (to_dual b) := hb 

end dual 

section circuit_hyperplane

/-- A circuit is a minimal dependent element-/
def circuit (x : α) := x ∈ minimals (≤) (indep : set α)ᶜ 

/-- A hyperplane is a maximally nonspanning element-/
def hyperplane (x : α) := x ∈ maximals (≤) (spanning : set α)ᶜ

lemma circuit.not_indep (hc : circuit c) : ¬ indep c := hc.1 

lemma circuit.dep (hc : circuit c) : dep c := hc.1 

lemma circuit.eq_of_dep_le (hc : circuit c) (hd : dep d) (hdc : d ≤ c) : d = c := (hc.2 hd hdc).symm

lemma circuit.indep_of_lt (hc : circuit c) (hic : i < c) : indep i := 
by_contra (λ h, hic.ne (hc.eq_of_dep_le h hic.le))
  
lemma circuit_antichain : is_antichain (≤) (circuit : set α) := 
λ _ h _ h' hne hle, hne (h'.eq_of_dep_le h.dep hle)
   
lemma hyperplane.not_spanning (hf : hyperplane f) : ¬ spanning f := hf.1 

lemma hyperplane.eq_of_le_nonspanning (hf : hyperplane f) (hx : ¬spanning x) (hfx : f ≤ x) : 
  f = x := hf.2 hx hfx

lemma hyperplane.spanning_of_lt (hf : hyperplane f) (hlt : f < s) : spanning s := 
by_contra (λ h, hlt.ne (hf.eq_of_le_nonspanning h hlt.le))
  
lemma hyperplane_antichain : is_antichain (≤) (hyperplane : set α) := 
λ f h f' h' hne hle, hne (h.eq_of_le_nonspanning h'.not_spanning hle)

end circuit_hyperplane

end base_family