import .easy_lemmas 
import order.minimal 
import order.upper_lower 
import order.modular_lattice 
import data.finite.basic
import order.atoms

universes u v 

variables {α : Type u}

open set order_dual 

section basis_family 

/-- A `basis_family` is a nonempty antichain -/
class basis_family (α : Type u) extends complete_lattice α := 
(carrier : set α)
(nonempty : carrier.nonempty)
(is_antichain : is_antichain (≤) carrier)

/-- A `basis_family` is also a basis family in the dual order -/
instance {α : Type u} [basis_family α]: basis_family αᵒᵈ := { 
carrier := of_dual ⁻¹' basis_family.carrier,
nonempty := basis_family.nonempty,
is_antichain := basis_family.is_antichain.to_dual }

variables [basis_family α] {x y i j a b b' c s t f d : α}

/-! #### Definitions / Existence -/ 
  
def basis (x : α) : Prop := x ∈ (basis_family.carrier : set α) 

/-- An element below a basis is independent-/
def indep (x : α) := ∃ b, basis b ∧ x ≤ b 

/-- An element above a basis is spanning-/
def spanning (x : α) :=  ∃ b, basis b ∧ b ≤ x 

/-- An element that is not independent is depedent-/
@[reducible] def dep (x : α) := ¬ indep x 

/-- A basis for `x` is a maximal element subject to being independent and below `x` -/
def basis_for (i x : α) := indep i ∧ i ≤ x ∧ ∀ j, indep j → j ≤ x → i ≤ j → i = j 

/-- A super for `x` is a minimal element subject to being spanning and above `t` -/
def super_for (s x : α) := spanning s ∧ x ≤ s ∧ ∀ t, spanning t → x ≤ t → t ≤ s → s = t

/-- A circuit is a minimal dependent element-/
def circuit (x : α) := x ∈ minimals (≤) (indep : set α)ᶜ 

/-- A hyperplane is a maximally nonspanning element-/
def hyperplane (x : α) := x ∈ maximals (≤) (spanning : set α)ᶜ

/-- `x` spans `y` if some basis for `y` is below `x` -/
def spans (x y : α) := ∃ i, basis_for i y ∧ i ≤ x

/-- `x` controls `y` if `y` is below some super for `x` -/
def controls (x y : α) := ∃ s, super_for s x ∧ y ≤ s

def rk_zero (x : α) := ∀ b, basis b → b ⊓ x = ⊥ 

lemma indep.not_dep (hi : indep i) : ¬ dep i := by rwa [not_not]

lemma dep.not_indep (hx : dep x) : ¬ indep x := hx 

lemma not_dep_iff_indep : ¬ dep i ↔ indep i  := by rw [not_not]
  
lemma indep_or_dep (i : α) : indep i ∨ dep i := em _  

lemma not_indep_iff_dep : ¬ indep i ↔ dep i := iff.rfl 

lemma indep.basis_for (hi : indep i) (hix : i ≤ x) (h : ∀ j, indep j → j ≤ x → i ≤ j → i = j) : 
  basis_for i x :=
⟨hi,  hix, h⟩

@[simp] lemma mem_lower_set_basis_iff_indep : indep i ↔ i ∈ lower_closure (basis : set α) := 
⟨λ ⟨b,hb,hbx⟩, ⟨b,hb,hbx⟩, λ ⟨b,hb,hbx⟩, ⟨b,hb,hbx⟩⟩

lemma spanning.super_for (hs : spanning s) (hxs : x ≤ s) 
  (h : ∀ t, spanning t → x ≤ t → t ≤ s → s = t) : super_for s x :=
⟨hs, hxs, h⟩

lemma basis.indep (h : basis b) : indep b := ⟨b, h, rfl.le⟩ 

lemma exists_basis (α : Type u) [basis_family α] : ∃ (b : α), basis b := basis_family.nonempty

lemma exists_indep : ∃ (i : α), indep i := (exists_basis α).imp (λ b hb, ⟨b,hb,rfl.le⟩)

lemma basis_for.indep (h : basis_for b x) : indep b := h.1

lemma basis_for.le (h : basis_for b x) : b ≤ x := h.2.1

@[simp] lemma mem_upper_set_basis_iff_spanning : s ∈ upper_closure (basis : set α) ↔ spanning s := 
⟨λ ⟨b,hb,hbx⟩, ⟨b,hb,hbx⟩, λ ⟨b,hb,hbx⟩, ⟨b,hb,hbx⟩⟩

lemma super_for_iff : 
  super_for s x ↔ spanning s ∧ x ≤ s ∧ ∀ s', spanning s' → x ≤ s' → s' ≤ s → s = s' := iff.rfl 

/-! #### Monotonicity  -/

lemma spanning.spanning_of_le (hs : spanning s) (hst : s ≤ t) : spanning t := 
exists.elim hs (λ b hb, ⟨b, hb.1, hb.2.trans hst⟩)

lemma spanning.sup_right_spanning (hs : spanning s) (x : α) : spanning (s ⊔ x) := 
hs.spanning_of_le le_sup_left 

lemma spanning.sup_left_spanning (hs : spanning s) (x : α) : spanning (x ⊔ s) := 
hs.spanning_of_le le_sup_right

lemma basis.spanning (h : basis b) : spanning b := ⟨b, h, rfl.le⟩

lemma basis.spanning_of_le (h : basis b) (hbs : b ≤ s) : spanning s := 
  h.spanning.spanning_of_le hbs 

lemma basis.sup_right_spanning (hb : basis b) (x : α) : spanning (b ⊔ x) := 
hb.spanning.sup_right_spanning _ 

lemma basis.sup_left_spanning (hb : basis b) (x : α) : spanning (x ⊔ b) := 
hb.spanning.sup_left_spanning _

lemma indep.indep_of_le (hi : indep i) (hji : j ≤ i) : indep j := 
exists.elim hi (λ b hb, ⟨b, ⟨hb.1, hji.trans hb.2⟩⟩)

lemma indep.inf_left_indep (hi : indep i) (x : α) : indep (x ⊓ i) := 
hi.indep_of_le inf_le_right

lemma indep.inf_right_indep (hi : indep i) (x : α) : indep (i ⊓ x) := 
hi.indep_of_le inf_le_left

lemma bot_indep (α : Type u) [basis_family α] : indep (⊥ : α) := 
exists.elim (exists_basis α) (λ b h, ⟨b, h, bot_le⟩)

lemma dep.dep_of_lt (hx : dep x) (hxy : x ≤ y) : dep y := 
not_indep_iff_dep.mp (λ h, (hx.not_indep (h.indep_of_le hxy)).elim)

lemma basis.indep_of_le (hb : basis b) (hi : i ≤ b) : indep i := ⟨b,hb,hi⟩ 

lemma basis.inf_left_indep (hb : basis b) (x : α) : indep (x ⊓ b) := 
hb.indep.indep_of_le inf_le_right

lemma basis.inf_right_indep (hb : basis b) (x : α) : indep (b ⊓ x) := 
hb.indep.indep_of_le inf_le_left

lemma top_spanning (α : Type u) [basis_family α] : spanning (⊤ : α) := 
exists.elim (exists_basis α) (λ b hb, ⟨b,hb,le_top⟩)

/-! #### Extremality -/

lemma basis_antichain : is_antichain (≤) (basis : set α) := basis_family.is_antichain 

lemma basis.eq_of_le_basis (hb : basis b) (hx : basis x) (hxb : b ≤ x) : b = x :=
by_contra (λ hne, basis_antichain hb hx hne hxb)

lemma basis.eq_of_le_indep (hb : basis b) (hi : indep i) (hbi : b ≤ i) : b = i := 
hbi.antisymm (exists.elim hi (λ b' ⟨hb',hib'⟩,(hb.eq_of_le_basis hb' (hbi.trans hib')).substr hib'))

lemma basis.eq_of_spanning_le (hb : basis b) (hs : spanning s) (hsb : s ≤ b) : s = b :=
hsb.antisymm (exists.elim hs (λ b' ⟨hb',hb's⟩, (hb'.eq_of_le_basis hb (hb's.trans hsb)).subst hb's))

lemma basis.not_indep_of_lt (hb : basis b) (hbx : b < x) : ¬ indep x := 
λ hx, hbx.ne (hb.eq_of_le_indep hx hbx.le)

lemma spanning.eq_of_le_basis (hs : spanning s) (hb : basis b) (hsb : s ≤ b) : s = b :=
hb.eq_of_spanning_le hs hsb 

lemma super_for.spanning (h : super_for s x) : spanning s := h.1 

lemma super_for.le (h : super_for s x) : x ≤ s := h.2.1 

lemma super_for.eq_of_spanning_le (hs : super_for s x) (hxt : x ≤ t) (hts : t ≤ s) 
  (ht : spanning t) : t = s := (hs.2.2 _ ht hxt hts).symm

lemma super_for.not_spanning_of_lt (hs : super_for s x) (hts : t < s) (hxt : x ≤ t):
  ¬ spanning t := 
λ h, hts.ne (hs.eq_of_spanning_le hxt hts.le h)

lemma basis_iff_maximal_indep : basis b ↔ (maximals (≤) indep) b := 
⟨λ hb, ⟨hb.indep,λ i hi hbi, hb.eq_of_le_indep hi hbi⟩, 
  λ ⟨⟨b',hb',hbb'⟩, hb''⟩, (hb'' hb'.indep hbb').substr hb'⟩

lemma basis_iff_minimal_spanning : basis b ↔ (minimals (≤) spanning) b :=
⟨λ hb, ⟨hb.spanning,λ s hs hbs, (hb.eq_of_spanning_le hs hbs).symm⟩, 
  λ ⟨⟨b',hb',hbb'⟩, hb''⟩, (hb'' hb'.spanning hbb').substr hb'⟩

lemma basis_for.eq_of_le_indep (h : basis_for b x) (hy : indep y) (hby : b ≤ y) (hyx : y ≤ x) : 
  b = y := (h.2.2 _ hy hyx hby)

lemma basis_for.not_indep_of_lt (hb : basis_for b x) (hby : b < y) (hyx : y ≤ x) : ¬ indep y := 
λ h, hby.ne (hb.eq_of_le_indep h hby.le hyx)

lemma basis_for.indep_of_le (hb : basis_for b x) (hib : i ≤ b)  : indep i := 
(hb.indep).indep_of_le hib 

lemma basis.basis_for_top [order_top α] (hb : basis b) : basis_for b ⊤ := 
hb.indep.basis_for le_top (λ j hj hbj h, hb.eq_of_le_indep hj h) 
    
lemma basis.lt_not_basis (hb : basis b) (hbx : b < x) : ¬ basis x := 
λ hx, (hb.not_indep_of_lt hbx hx.indep)

lemma basis.not_basis_for_lt (hb : basis b) (hxb : x < b) : ¬ basis x := 
λ h, (h.lt_not_basis hxb) hb 

lemma indep.basis (hi : indep i) (hmax : ∀ j, indep j → i ≤ j → i = j) : basis i := 
exists.elim hi (λ b ⟨hb, hbi⟩, (hmax b hb.indep hbi).substr hb)

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

section dual 

lemma indep.spanning_dual (hi : indep i) : spanning (to_dual i) := hi 

@[simp] lemma spanning_dual_iff_indep : spanning (to_dual i) ↔ indep i := iff.rfl 

lemma spanning.indep_dual (hs : spanning s) : indep (to_dual s) := hs

@[simp] lemma indep_dual_iff_spanning : indep (to_dual s) ↔ spanning s := iff.rfl 

lemma basis.to_dual (hb : basis b) : basis (to_dual b) := hb 

end dual 

/-- In a matroid on a finite lattice, bases for sets exist -/
lemma indep.le_basis_for_of_le_of_finite [finite α] {i x : α} (hi : indep i) (hix : i ≤ x) : 
∃ j, basis_for j x ∧ i ≤ j := 
(set.finite.exists_maximal_mem 
  (⟨i, ⟨hi,rfl.le,hix⟩⟩ : {i' | indep i' ∧ i ≤ i' ∧ i' ≤ x}.nonempty)).imp 
    (λ j ⟨⟨hj, hij,hjx⟩,hj_max⟩, 
     ⟨⟨hj,hjx, λ j' hj' hj'x hjj', hj_max j' ⟨hj',hij.trans hjj',hj'x⟩ hjj'⟩, hij⟩)

/-- In a matroid on a finite lattice, supers for sets exist -/
lemma spanning.super_of_le_of_le_of_finite [finite α] {s x : α} (hs : spanning s) (hxs : x ≤ s) :
∃ t, super_for t x ∧ t ≤ s := 
@indep.le_basis_for_of_le_of_finite αᵒᵈ _ _ _ _ hs hxs

end basis_family

section supermatroid_family 

/-- Class for basis families that satisfy an augmentation axiom. Equivalent to independence 
augmentation in the case of finite set lattices. -/
class supermatroid_family (α : Type u) extends basis_family α, is_modular_lattice α :=
(exists_basis_between_of_indep_le_spanning : 
  ∀ (x y : α), indep x → spanning y → x ≤ y → ∃ b, basis b ∧ x ≤ b ∧ b ≤ y) 
(le_basis_for_of_indep_le : ∀ (i x : α), indep i → i ≤ x → ∃ j, basis_for j x ∧ i ≤ j)
  
variables [supermatroid_family α] {i b b' s x y : α}

/-- A basis_family on a finite lattice that satisfies the middle axiom is a supermatroid family -/
noncomputable lemma supermatroid_family_of_finite {α : Type u} [basis_family α] [finite α] 
[is_modular_lattice α] 
(h : ∀ (x y : α), indep x → spanning y → x ≤ y → ∃ b, basis b ∧ x ≤ b ∧ b ≤ y) : 
  supermatroid_family α :=
⟨h, @indep.le_basis_for_of_le_of_finite _ _ _⟩ 

/-- #### Extensions to bases -/

lemma indep.exists_basis_between_of_le_spanning (hi : indep i) (hs : spanning s) (his : i ≤ s) : 
  ∃ b, basis b ∧ i ≤ b ∧ b ≤ s := 
supermatroid_family.exists_basis_between_of_indep_le_spanning _ _ hi hs his  

lemma basis.exists_basis_of_subset_le_supset_basis (hb : basis b) (hb' : basis b') (hxy : x ≤ y) 
  (hxb : x ≤ b) (hb'y : b' ≤ y): 
   ∃ b₀, basis b₀ ∧ x ≤ b₀ ∧ b₀ ≤ y :=
supermatroid_family.exists_basis_between_of_indep_le_spanning _ _ ⟨b,hb,hxb⟩ ⟨b',hb',hb'y⟩ hxy 

lemma indep.lt_basis_le_spanning_of_not_basis (hi : indep i) (hi_b : ¬basis i) (hs : spanning s)
(his : i ≤ s) :
  ∃ b, basis b ∧ i < b ∧ b ≤ s  := 
(hi.exists_basis_between_of_le_spanning hs his).imp 
  (λ j, λ ⟨hj,hij,hjs⟩, ⟨hj, hij.lt_of_ne (λ h, hi_b (h.substr hj)), hjs⟩)

lemma indep.lt_basis_sup_le_sup_basis_of_not_basis (hi : indep i) (hi_nb : ¬ basis i) 
(hb : basis b) :
  ∃ b', basis b' ∧ i < b' ∧ b' ≤ i ⊔ b :=
(hi.lt_basis_le_spanning_of_not_basis hi_nb (hb.sup_left_spanning _) le_sup_left)

lemma indep.basis_of_spanning (hi : indep i) (hs : spanning i) : basis i := 
exists.elim (hi.exists_basis_between_of_le_spanning hs rfl.le) 
  (λ a ⟨ha,hia,hai⟩, (hai.antisymm hia).subst ha)

lemma indep.le_basis_for_of_le (hi : indep i) (hix : i ≤ x) : ∃ j, basis_for j x ∧ i ≤ j := 
supermatroid_family.le_basis_for_of_indep_le _ _ hi hix  

lemma basis_for.basis (hb : basis_for b s) (hs : spanning s) : basis b := 
exists.elim (hb.indep.exists_basis_between_of_le_spanning hs hb.le) 
  (λ b' ⟨hb',hbb',hb's⟩, (hb.eq_of_le_indep hb'.indep hbb' hb's).substr hb') 

lemma indep.le_basis_le_sup_basis (hi : indep i) (hb : basis b) : 
   ∃ b', basis b' ∧ i ≤ b' ∧ b' ≤ i ⊔ b :=
(hi.le_basis_for_of_le (@le_sup_left _ _ i b)).imp 
  (λ j ⟨hj,hij⟩, ⟨hj.basis (hb.sup_left_spanning _), hij, hj.le⟩)

lemma exists_basis_for (x : α) : ∃ i, basis_for i x := 
exists.elim (exists_basis α) 
  (λ b hb, ((hb.inf_right_indep x).le_basis_for_of_le inf_le_right).imp (λ _ h, h.1)) 

lemma basis.inf_basis_for (hb : basis b) (x : α) : 
  ∃ b', basis b' ∧ (basis_for (b' ⊓ x) x) ∧ b' ≤ x ⊔ b  :=
begin
  obtain ⟨i,hi⟩ := exists_basis_for x, 
  obtain ⟨b',⟨hb',bib',hb'i⟩⟩ := hi.indep.le_basis_le_sup_basis hb,
  refine ⟨b',hb', 
    (hb'.inf_right_indep _).basis_for inf_le_right (λ j hj hjx hb'j, hb'j.antisymm (le_inf _ hjx)), 
    hb'i.trans (sup_le_sup_right hi.le _)⟩,
  rwa ←hi.eq_of_le_indep hj (le_trans (le_inf bib' hi.le) hb'j) hjx,  
end 

lemma basis.lt_basis_le_sup_basis_of_lt (hb : basis b) (hb' : basis b') (hib : i < b) :
  ∃ b₀, basis b₀ ∧ i < b₀ ∧ b₀ ≤ i ⊔ b' :=
(hb.indep_of_le hib.le).lt_basis_sup_le_sup_basis_of_not_basis (hb.not_basis_for_lt hib) hb' 

/-- #### Duality -/

private lemma spanning.super_for_le_of_le' (hs : spanning s) (hxs : x ≤ s) : 
  ∃ t, super_for t x ∧ t ≤ s :=
begin
  obtain ⟨b,hb,hbs⟩ := hs, 
  obtain ⟨b₁, hb₁, hb₁x, hb₁b⟩ := hb.inf_basis_for x, 
  refine ⟨x ⊔ b₁, ⟨hb₁.sup_left_spanning _, le_sup_left, _⟩, 
    sup_le hxs (hb₁b.trans (sup_le hxs hbs))⟩, 
  rintros t ⟨b₂,hb₂,hb₂t⟩ hxt hty,
  refine (sup_le hxt (by_contra (λ hb₁t, _))).antisymm hty,   
  set j := b₁ ⊓ (x ⊔ b₂) with hj, 

  have hj_lt : j < b₁ := inf_le_left.lt_of_ne 
    (λ h_eq, hb₁t (by {rw ← h_eq, exact inf_le_right.trans (sup_le hxt hb₂t)})),   
  
  obtain ⟨b₃, hb₃, hjb₃, hb₃j⟩ := hb₁.lt_basis_le_sup_basis_of_lt hb₂ hj_lt, 

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
instance : supermatroid_family αᵒᵈ := 
⟨ λ i s hi hs his, 
  (indep.exists_basis_between_of_le_spanning hs hi his).imp (λ b ⟨hb,hsb,hbi⟩, ⟨hb, hbi, hsb⟩), 
  λ i x hi hix, (spanning.super_for_le_of_le' hi hix).imp (λ a ⟨ha, hia⟩, ⟨ha, hia⟩)⟩

/-- #### Spanning sets -/

lemma spanning.basis_lt_indep_le_of_not_basis (hs : spanning s) (hs_nb : ¬basis s) (hi : indep i) 
(his : i ≤ s) : 
  ∃ b, basis b ∧ b < s ∧ i ≤ b := 
@indep.lt_basis_le_spanning_of_not_basis αᵒᵈ _ _ _ hs hs_nb hi his

lemma spanning.basis_lt_inf_basis_le_of_not_basis (hs : spanning s) (hs_nb : ¬basis s)
(hb : basis b) : 
  ∃ b', basis b' ∧ b' < s ∧ s ⊓ b ≤ b' := 
@indep.lt_basis_sup_le_sup_basis_of_not_basis αᵒᵈ _ _ _ hs hs_nb hb 

lemma super_for.basis (hs : super_for s x) (hx : indep x) : basis s :=
@basis_for.basis αᵒᵈ _ _ _ hs hx

lemma spanning.super_for_le_of_le (hs : spanning s) (hxs : x ≤ s) : ∃ t, super_for t x ∧ t ≤ s :=
spanning.super_for_le_of_le' hs hxs

lemma spanning.basis_le_basis_inf_le (hs : spanning s) (hb : basis b) :
  ∃ b', basis b' ∧ b' ≤ s ∧ s ⊓ b ≤ b' := 
@indep.le_basis_le_sup_basis αᵒᵈ _ _ _ hs hb 

lemma basis.basis_lt_inf_le_basis_of_lt (hb : basis b) (hb' : basis b') (hbs : b < s) : 
  ∃ b₀, basis b₀ ∧ b₀ < s ∧ s ⊓ b' ≤ b₀ := 
@basis.lt_basis_le_sup_basis_of_lt αᵒᵈ _ _ _ _ hb hb' hbs 

lemma basis.sup_super_for (hb : basis b) (x : α) :
  ∃ b',basis b' ∧ super_for (b' ⊔ x) x ∧ x ⊓ b ≤ b'  :=
@basis.inf_basis_for αᵒᵈ _ _ hb x

section atoms

variables [is_atomistic α] [is_coatomistic α]

lemma foo (h : ∀ {x y i : α}, basis_for i x → basis_for i y → basis_for i (x ⊔ y)) :
(∀ {x y s : α}, super_for s x → super_for s x → super_for s (x ⊓ y)) :=

begin

end 

end atoms

end supermatroid_family
