import .supermatroid_minor
import order.zorn

universes u v 

open set 

variables {α : Type u} {κ : Type v}

section qmatroid 

/-- A `qmatroid` is a `supermatroid` with some lattice-closure conditions on the set of elements
spanned by an independent set i -/
class qmatroid (α : Type u) extends supermatroid α := 
(basis_sup : ∀ (i x y : α), i basis_for x → i basis_for y → i basis_for x ⊔ y)
(basis_Sup_chain : ∀ (i C), 
  is_chain (≤) C → C.nonempty → (∀ (x ∈ C), i basis_for x) → i basis_for (Sup C))
(canopy_Inf_chain : ∀ (s C), 
  is_chain (≤) C → C.nonempty → (∀ (x ∈ C), s canopy_for x) → s canopy_for (Inf C))

variables [qmatroid α] {S : set α} {i j x y x' y' z z' s t a b : α} {f : α → α}

lemma basis_for.sup (hx : i basis_for x) (hy : i basis_for y) : i basis_for x ⊔ y := 
qmatroid.basis_sup _ _ _ hx hy 

lemma indep.basis_Sup_basis (hi : indep i) : i basis_for Sup {x | i basis_for x} :=
begin
  obtain ⟨u, hub, hu⟩ := @zorn_partial_order₀ α _ {x | i basis_for x} 
    (λ C hCb hC, C.eq_empty_or_nonempty.elim 
      (by {rintro rfl, exact ⟨i, hi.basis_self, by simp⟩, })
      (λ hC_ne, ⟨Sup C, qmatroid.basis_Sup_chain _ _ hC hC_ne hCb, λ _, le_Sup⟩)), 
  rwa (le_Sup hub).antisymm'   
    (Sup_le (λ x hx, sup_eq_right.mp (hu _ (basis_for.sup hx hub) le_sup_right))), 
end 

lemma basis_Sup_of_forall (hS : S.nonempty) (h : ∀ x ∈ S, i basis_for x) : 
  i basis_for (Sup S) := 
(exists.elim hS (λ x hx, (h x hx).indep)).basis_Sup_basis.basis_of_le 
  (exists.elim hS (λ x hx, (h x hx).le.trans (le_Sup hx)))
  (Sup_le (λ x hx, le_Sup (h x hx)))

lemma basis_bsupr_of_forall (hS : S.nonempty) (h : ∀ x ∈ S, i basis_for (f x)) : 
  i basis_for (⨆ (x ∈ S), f x) :=
by {rw ←Sup_image, exact basis_Sup_of_forall (hS.image _) (λ x ⟨y,hy,hyx⟩, 
      by {rw ← hyx, exact h _ hy})}

lemma basis_supr_of_forall [nonempty κ] {x : κ → α} (h : ∀ k, i basis_for (x k)) :
  i basis_for (⨆ k, x k) :=
basis_Sup_of_forall (range_nonempty x) (λ y ⟨k,hk⟩,hk.subst (h k))

lemma basis_Sup_of_forall_sup (hS : S.nonempty) (h : ∀ x ∈ S, i basis_for (x ⊔ i)) : 
  i basis_for (Sup S ⊔ i) := 
by {rw [Sup_eq_supr, ←bsupr_sup hS], exact basis_bsupr_of_forall hS h} 
  
lemma indep.basis_Sup_of_forall_sup (hi : indep i) (h : ∀ x ∈ S, i basis_for x ⊔ i) : 
  i basis_for (Sup S) ⊔ i := 
S.eq_empty_or_nonempty.elim (by {rintro rfl, simpa using hi.basis_self}) 
  (λ hS, basis_Sup_of_forall_sup hS h)

lemma basis_for.basis_sup_of_basis (hx : i basis_for x) (hy : i basis_for y) : 
  i basis_for (x ⊔ y) := 
by {rw sup_eq_supr, exact basis_supr_of_forall (λ k, by {cases k; assumption})}

lemma indep.basis_closure (hi : indep i) : i basis_for (closure i) := 
begin
  rw [←sup_eq_left.mpr (le_closure_self i)], 
  exact basis_Sup_of_forall_sup ⟨i, by simp⟩ (λ x hx, hx i hi.basis_self),
end 

lemma basis_for.basis_closure (hix : i basis_for x) : i basis_for (closure x) :=
begin
  rw [←sup_eq_left.mpr (hix.le.trans (le_closure_self x))], 
  refine basis_Sup_of_forall_sup ⟨x, by simp⟩ (λ y hy, _), 
  exact (hy _ hix).basis_of_le le_sup_right (sup_le_sup_left hix.le _), 
end 

lemma indep.basis_sup_of_le_closure (hi : indep i) (hxi : x ≤ closure i) : 
  i basis_for (i ⊔ x) :=
hi.basis_closure.basis_of_le le_sup_left (sup_le (le_closure_self i) hxi)

lemma spans_closure_self (x : α) : x spans (closure x) := 
begin
  rintros i hi, 
  rw [sup_eq_left.mpr (le_closure_self x), ←sup_eq_left.mpr (hi.le.trans (le_closure_self x))], 
  exact hi.indep.basis_Sup_of_forall_sup 
    (λ y hy, (hy i hi).basis_of_le le_sup_right (sup_le_sup_left hi.le _)), 
end

lemma basis_for.basis_of_basis_basis_le (hix : i basis_for x) (hiy : i basis_for y)
(hjx : j basis_for x) (hjy : j ≤ y) :
  j basis_for y :=
begin
  obtain ⟨j',hj',hjj'⟩ := hjx.indep.le_basis_of_le hjy,
  refine hjj'.lt_or_eq.elim (λ hlt, by_contra (λ hjy', _)) (λ h, h.substr hj'), 
  obtain ⟨k,hk,hjk,hki⟩ := hjx.indep.lt_basis_le_sup_of_not_basis hjy' hiy hjy, 
  exact hjx.not_indep_of_lt hjk (hki.trans (sup_le hjx.le hix.le)) hk.indep, 
end 

lemma basis_for.basis_sup_of_le_closure (hix : i basis_for x) (hyx : y ≤ closure x) : 
  i basis_for (y ⊔ i) :=
((spans_closure_self x).basis_for hix).basis_of_le le_sup_right (sup_le_sup hyx hix.le)
 
lemma basis_for.spans_iff_basis_sup (hi : i basis_for x) : 
  x spans y ↔ i basis_for (y ⊔ i) :=
begin
  refine ⟨λ h, (h _ hi).basis_of_le le_sup_right (sup_le_sup_left hi.le _), λ h j hj, _⟩,
  refine (hi.basis_of_basis_basis_le (hi.basis_sup_of_basis h) hj 
    (hj.le.trans le_sup_left)).basis_of_le 
    (hj.le.trans le_sup_right) (by {rw sup_comm, exact sup_le_sup_left le_sup_left _}), 
end 

lemma basis_for.le_closure_iff_basis_sup (hix : i basis_for x): 
  y ≤ closure x ↔ i basis_for (y ⊔ i)  :=
begin
  refine ⟨hix.basis_sup_of_le_closure,λ h, le_Sup (λ j hj, _)⟩, 
  exact (hix.basis_of_basis_basis_le (hix.basis_sup_of_basis h) hj 
    (hj.le.trans le_sup_left)).basis_of_le 
    (hj.le.trans le_sup_right) (by {rw sup_comm, exact sup_le_sup_left le_sup_left _}), 
end 

lemma spans_iff_le_closure : 
  x spans y ↔ y ≤ closure x :=
by {obtain ⟨i,hi⟩ := exists_basis x, 
  rw [hi.le_closure_iff_basis_sup, hi.spans_iff_basis_sup]}

lemma basis_for.spans_of_basis_sup (hix : i basis_for x) (hiy : i basis_for (y ⊔ i)) :
  x spans y := 
hix.spans_iff_basis_sup.mpr hiy 

lemma spans.mono_right (hxy : x spans y) (hy'y : y' ≤ y) : x spans y' :=
λ i hix, (hxy _ hix).basis_of_le (le_sup_of_le_right hix.le) (sup_le_sup_right hy'y _)
 
lemma spans.mono_left (hxy : x spans y) (hxx' : x ≤ x') : x' spans y :=
begin
  obtain ⟨i,hi⟩ := exists_basis x, 
  obtain ⟨i',hi',hii'⟩ := hi.indep.le_basis_of_le (hi.le.trans hxx'),
  exact hi'.spans_of_basis_sup 
   (((hxy.basis_for hi).basis_sup_mono hi'.indep hii').basis_of_le le_sup_right 
    (sup_le_sup_right le_sup_left _)), 
end 

lemma spans.mono (hxy : x spans y) (hxx' : x ≤ x') (hy'y : y' ≤ y) : x' spans y' :=
(hxy.mono_left hxx').mono_right hy'y

lemma spans_bot (x : α) : x spans ⊥ := λ i hi, by rwa bot_sup_eq

lemma spans_iff_exists : 
  x spans y ↔ ∃ i, i basis_for (y ⊔ i) ∧ i ≤ x :=
⟨λ h, (exists_basis x).imp (λ i hi, ⟨hi.spans_iff_basis_sup.mp h,hi.le⟩), 
  λ ⟨i, hi, hix⟩, spans.mono_left (hi.indep.basis_self.spans_of_basis_sup hi) hix⟩

lemma basis_for.spans_of_basis (hi : i basis_for x) (hiy : i basis_for (y ⊔ i)) : x spans y :=
  spans_iff_exists.mpr ⟨i, hiy, hi.le⟩ 

lemma basis_for.spans (hi : i basis_for x) : i spans x := 
spans_iff_exists.mpr ⟨i, hi.basis_sup_self, rfl.le⟩ 

lemma basis_for.spans_right (hi : i basis_for x) : x spans i := 
spans_iff_exists.mpr ⟨i , sup_idem.substr hi.indep.basis_self, hi.le⟩
  
lemma spanning_iff_spans_top : spanning s ↔ s spans (⊤ : α) :=  
by simp_rw [spans_iff_exists, spanning_iff_basis_le, top_sup_eq, basis_top_iff]

lemma indep.basis_sup_of_spans (hi : indep i) (hix : i spans x) : i basis_for x ⊔ i := 
begin
  obtain ⟨i',hi',hi'i⟩ := spans_iff_exists.mp hix, 
  refine (hi'.basis_sup_mono hi hi'i).basis_of_le le_sup_right _,
  rw sup_right_comm, exact le_sup_left, 
end 

lemma indep.basis_of_spans_le (hi : indep i) (hix : i spans x) (hle : i ≤ x) : i basis_for x := 
(sup_eq_left.mpr hle) ▸ (hi.basis_sup_of_spans hix)

lemma closure_idem (x : α) : closure (closure x) = closure x :=
begin
  refine le_antisymm _ (le_closure_self _), 
  obtain ⟨i,hi⟩ := exists_basis x, 
  rw [hi.le_closure_iff_basis_sup, 
    sup_eq_left.mpr (hi.le.trans ((le_closure_self x).trans (le_closure_self _)))],
  exact basis_for.basis_closure (basis_for.basis_closure hi), 
end 

lemma indep.inf_Sup_basis_Sup_of_forall_inf_basis (hi : indep i)
(hS : ∀ x ∈ S, (x ⊓ i) basis_for x) : 
  (Sup S ⊓ i) basis_for (Sup S) :=
begin
  refine S.eq_empty_or_nonempty.elim (by {rintro rfl, simpa using (bot_indep α).basis_self}) 
    (λ hS_ne, _), 
  
  obtain ⟨k,hk,hkS⟩ := (hi.inf_left_indep (Sup S)).le_basis_of_le inf_le_left, 
  have hxS := λ {x : α} (hx : x ∈ S), (hS x hx).eq_of_le_indep (hk.indep.inf_left_indep x) 
    (le_inf inf_le_left (le_trans (inf_le_inf_right _ (le_Sup hx)) hkS)) inf_le_left,   
  
  have hb := λ x hx, (hS x hx).basis_sup_mono (hi.inf_left_indep (Sup S))
    (inf_le_inf_right i (le_Sup hx)), 
  refine (basis_bsupr_of_forall hS_ne hb).basis_of_le inf_le_left _,  
  rw ←Sup_image, 
  refine Sup_le_Sup_of_forall_exists_le (λ x hx, _), 
  simp only [mem_image, exists_prop, exists_exists_and_eq_and], 
  refine ⟨x,hx, le_sup_left⟩,
end 

lemma supr_basis_supr_of_forall {i x : κ → α} 
(h : ∀ k, (i k) basis_for (x k)) (hind : indep (⨆ k, (i k))) : 
  (⨆ k, i k) basis_for (⨆ k, x k) :=
begin
  refine hind.basis_for (supr_le (λ k, (h k).le.trans (le_supr _ _))) (λ j hj hjle hi'j, _), 
  set i' := ⨆ k, i k with hi', 
  have h' : ∀ k, (i k) = (x k)  ⊓ i' := λ k, (h k).eq_of_le_indep 
    (hind.inf_left_indep _) (le_inf (h k).le (le_supr _ _) ) inf_le_left,
  simp_rw h' at h, 
  have hb := @indep.inf_Sup_basis_Sup_of_forall_inf_basis _ _ (range x) _ hind
    (λ y ⟨z,hz⟩, by {simpa [hz] using h z}),  
  obtain rfl := hb.eq_of_le_indep hj (le_trans inf_le_right hi'j) hjle, 
  exact hi'j.antisymm inf_le_right, 
end 

lemma basis_for.baz (hi : i basis_for x) (hj : j basis_for y) (hij : indep (i ⊔ j)) : 
  (i ⊔ j) basis_for (x ⊔ y) :=
begin
  have := @supr_basis_supr_of_forall _ _ _ (λ b, cond b i j) (λ b, cond b x y) 
    (λ k, by {cases k; simpa}), 
  simp only [supr_bool_eq] at this, 
  exact this hij, 
end 

lemma basis_for.baz' (hi : i basis_for x) (hj : j basis_for y) (hij : i ≤ j) : 
  j basis_for (x ⊔ y) :=
let hij' := sup_eq_right.mpr hij in by {convert hi.baz hj (by {rw hij', exact hj.indep}), rw hij'} 

lemma closure_mono (hxy : x ≤ y) : closure x ≤ closure y :=
begin
  obtain ⟨i,hi⟩ := exists_basis x, 
  obtain ⟨j, hj, hij⟩ := hi.indep.le_basis_of_le (hi.le.trans hxy), 
  exact hj.le_closure_iff_basis_sup.mpr  
    (basis_Sup_of_forall_sup (⟨x, λ hk, by {rw sup_idem, exact id}⟩) 
      (λ z hz, ((hz _ hi).baz' hj hij).basis_of_le le_sup_right 
        (sup_assoc.substr (sup_le_sup_left (le_sup_of_le_right hj.le) _)))), 
end 

lemma spans.trans (hxy : x spans y) (hyz : y spans z) : x spans z :=
begin
  obtain ⟨i,hi⟩ := exists_basis x, 
  refine basis_for.spans_of_basis_sup hi _, 
  have hb := (hxy.basis_for hi).basis_of_le le_sup_right (sup_le_sup_left hi.le y),  
  exact ((hyz.mono_left le_sup_left) i hb).basis_of_le le_sup_right 
    (sup_le_sup_left le_sup_right _), 
end 

lemma spanning.spanning_of_spans (hs : spanning s) (hxs : x spans s) : spanning x :=
by {rw spanning_iff_spans_top at *, exact hxs.trans hs}

lemma base.spanning_of_spans (hb : base b) (hxb : x spans b) : spanning x :=
hb.spanning.spanning_of_spans hxb

lemma supr_spans_supr_of_forall {a x : κ → α} (h : ∀ k, a k spans x k) : 
  (⨆ k, a k) spans (⨆ k, x k) :=
begin
  refine (is_empty_or_nonempty κ).elim (λ he, _ ) (λ hk, _),
  { simp_rw @supr_of_empty _ _ _ he, exact spans_bot _, },
  obtain ⟨i, hi⟩ := exists_basis (⨆ k, a k),  
  have h1 := λ k, (hi.spans.mono_right (le_supr _ _)).trans (h k), 
  have h2 := (λ k, hi.indep.basis_sup_of_spans (h1 k)),  
  have h3 := (@basis_supr_of_forall α _ _ _ hk _ h2).spans,  
  refine (hi.spans_right.trans h3).mono_right _, 
  rw [←(@supr_sup _ _ _ hk)], exact le_sup_left, 
end 

lemma spans_Sup_of_forall (h : ∀ x ∈ S, a spans x) : a spans (Sup S) :=
begin
  refine S.eq_empty_or_nonempty.elim (by {rintro rfl, simpa using spans_bot _}) (λ hS, _),
  convert @supr_spans_supr_of_forall α S _ (λ _, a) coe (λ ⟨x,hx⟩, h x hx), 
  exact (@supr_const _ S _ _ (hS.to_subtype)).symm, 
  simp, 
end 

lemma spans.sup (ha : a spans x) (hb : b spans y) : (a ⊔ b) spans (x ⊔ y) :=
begin
  rw [sup_eq_supr, sup_eq_supr], 
  exact @supr_spans_supr_of_forall _ _ _ (λ i, cond i a b) (λ i, cond i x y) 
    (λ i, by {cases i; assumption}), 
end

lemma bsupr_spans_Sup_of_forall (h : ∀ x ∈ S, f x spans x) : (⨆ (x ∈ S), f x) spans Sup S :=
begin
  convert @supr_spans_supr_of_forall α S _ (λ z, f z) coe (λ (z : S), h z.1 z.2) using 1, 
  exact supr_subtype',
  rw [Sup_eq_supr, supr_subtype'], refl, 
end 

lemma basis_for.sup_canopy_of_le_base (hix : i basis_for x) (hb : base b) (hib : i ≤ b) : 
  (x ⊔ b) canopy_for x := 
by {obtain rfl := hix.eq_of_le_indep (hb.inf_left_indep x) (le_inf hix.le hib) inf_le_left, 
  rwa hb.sup_canopy_iff_inf_basis}

lemma sup_eq_sup_of_basis_basis_spans (hi_inf : x ⊓ i basis_for x) (hi_sup : i basis_for x ⊔ i) 
(hy : y spans x ⊔ i) (hy_le : y ≤ x ⊔ i): 
  x ⊔ y = x ⊔ i :=
begin
  obtain ⟨j,hj⟩ := exists_basis y, 
  have hj' := spans_iff_forall.mp hy _ hj, 
  rw [sup_eq_left.mpr hy_le] at hj', 
  have h' := sup_eq_of_basis_basis_basis hi_inf hi_sup hj', 
  rw [←h'], 
  exact (sup_le le_sup_left (by rwa h')).antisymm (sup_le le_sup_left (hj.le.trans le_sup_right)),
end 

section dual 

/-- This lemma is the minimum needed to bootstrap duality for q-matroids. Its generalization to 
  arbitrary indexing types will follow from duality. -/
private lemma closure_infi_eq_infi_closure_of_indep_bool {i : bool → α} (h : indep (⨆ t, i t)) : 
  (⨅ t, closure (i t)) = closure (⨅ t, i t) :=
begin
  refine le_antisymm _ (le_infi (λ t, closure_mono (infi_le _ _))), 
  rw [←spans_iff_le_closure, spans_iff_exists], 
  have h_indep := λ t, h.indep_of_le (le_supr _ t), 
  refine ⟨_, (h.indep_of_le ((infi_le _ tt).trans (le_supr _ _))).basis_for 
    le_sup_right (λ k hk hk_le hle_k, hle_k.antisymm _), rfl.le⟩, 

  rw [sup_eq_left.mpr 
    (le_infi (λ t, (infi_le _ _).trans (le_closure_self _)) : (⨅ t, i t) ≤ ⨅ t, closure (i t) ), 
    le_infi_iff] at hk_le,  
  simp_rw [←spans_iff_le_closure, spans_iff_forall] at hk_le, 
  have hforall_b := λ t, (hk_le t (i t) (h_indep t).basis_self), clear hk_le, 

  have heq_inf_supr : ∀ t, i t = (k ⊔ (i t)) ⊓ (⨆ t', i t') := 
    λ t, (hforall_b t).eq_of_le_indep (h.indep_of_le inf_le_right) 
      (le_inf le_sup_right (le_supr _ _)) inf_le_left,

  have h' : ∀ t, (i t) ⊓ (k ⊔ i (!t)) = (i (!t)) ⊓ (k ⊔ i t) := λ t, by 
    {nth_rewrite 1 [heq_inf_supr (!t)], nth_rewrite 0 [heq_inf_supr t], rw inf_left_right_swap},

  have h'' : ∀ t, (i t ⊓ (k ⊔ i (!t))) = ⨅ t', i t' := 
  begin
    intro t,  
    rw [←@inf_idem _ _ (i t ⊓ (k ⊔ i (!t)))], nth_rewrite 0 h', 
    rw [inf_left_comm, inf_right_comm, inf_eq_left.mpr (@le_sup_right _ _  k _), inf_left_comm, 
      inf_eq_left.mpr (@le_sup_right _ _ k _), inf_comm, infi_bool_eq'], 
  end, 
    
  have hk_eq : k = ⨅ t, (k ⊔ i t) := le_antisymm (le_infi (λ t, le_sup_left)) 
    (by rwa [infi_bool_eq, sup_comm, @sup_comm _ _ _ (i _), is_modular_lattice.sup_inf_sup_assoc, 
      inf_comm, @sup_comm _ _ (i _), ←bool.bnot_false, h', bool.bnot_false, ←bool.bnot_true, h'', 
      sup_eq_right.mpr]),

  have hwin : ∀ (t : bool), k ≤ i (!t) := λ t, by {
    obtain ⟨k', hk', hlek'⟩ := hk.le_basis_of_le (le_sup_left : k ≤ k ⊔ i (!t)), 
    have hspans : k' ⊔ i t spans k ⊔ i t ⊔ (⨆ t, i t), 
    { refine (hk'.spans.sup (spans_self (i t))).mono_right _,
      rw [sup_right_comm _ (i (!t)), supr_bool_eq' t, ←sup_assoc, @sup_assoc _ _ k (i t),sup_idem]}, 
    
    have hbig := @eq_of_le_of_inf_le_of_sup_le _ _ _  _ _ (k ⊔ i t) hk'.le 
    (by {rw [inf_comm, ←(infi_bool_eq' t), ←hk_eq], exact le_inf hlek' le_sup_left}) 
    (by {
      have hk'' := @sup_eq_sup_of_basis_basis_spans _ _ (⨆ t, i t) (k ⊔ i t) (k' ⊔ i t)
        (by {rw ←heq_inf_supr, exact hforall_b _})
        (by {refine h.basis_of_spans_le _ le_sup_right, 
          convert supr_spans_supr_of_forall (λ t, (hforall_b t).spans), 
          rw [supr_bool_eq' t, supr_bool_eq' t, ←sup_assoc, ←sup_assoc, @sup_assoc _ _ k, 
            sup_idem, sup_right_comm k (i t) k, sup_idem]})
        hspans 
        (sup_le (hk'.le.trans (sup_le (le_sup_of_le_left le_sup_left) 
          (le_sup_of_le_right (le_supr _ _)))) (le_sup_of_le_left le_sup_right)), 
      rw [sup_right_comm, sup_assoc, sup_assoc, sup_idem, ←sup_assoc, @sup_comm _ _ k] at hk'',
      rw [←@sup_assoc _ _ k', hk'', sup_comm, sup_right_comm, ←sup_assoc, sup_idem, sup_right_comm],
      exact sup_le_sup_left (le_supr _ _) _}),

    have hb' := hk'.indep.eq_of_basis (hbig.substr (hforall_b (!t))),
    rwa [hb', eq_comm, sup_eq_right] at hbig},

  refine le_infi (λ t, by {have := hwin (!t), rwa bnot_bnot at this}),
end 

private lemma canopy_infi_bool {x : bool → α} (h_can : ∀ k, s canopy_for (x k)) : 
  s canopy_for (⨅ k, x k) :=
begin
  obtain ⟨b,hb, (hsb : ∀ k, s = x k ⊔ b)⟩ := eq_sup_basis_forall_of_canopy_forall h_can, 

  have h_bas := λ k, hb.sup_canopy_iff_inf_basis.mp ((hsb k).subst (h_can k)),

  have hsupr_inf_basis : (⨆ k, ((x k) ⊓ b)) basis_for ⨆ k, x k := indep.basis_of_spans_le 
    (hb.indep_of_le (Sup_le (by simp)))
    (supr_spans_supr_of_forall (λ k, (h_bas k).spans))
    (supr_le (λ k, inf_le_left.trans (le_supr _ _))),
    
  have h_distrib : (⨆ k, x k ⊓ b) = (⨆ k, x k) ⊓ b := 
    hsupr_inf_basis.eq_of_le_indep (hb.inf_left_indep _) 
    (supr_le (λ k, inf_le_inf_right _ (le_supr _ _))) inf_le_left,  

  have h_distrib' : ∀ k, (x k ⊓ b) ⊔ (x (!k)) ⊓ b = (x k ⊔ x (!k)) ⊓ b :=   
    λ k, by rw [←supr_bool_eq' k, h_distrib, supr_bool_eq'],

  have hinf_sup_inf : ∀ k, x k = (x k) ⊓ b ⊔ ((x k) ⊓ (x (!k))) := 
  begin
    intro k, 
    rw [inf_comm, @inf_comm _ _ _ (x (!k)), is_modular_lattice.inf_sup_inf_assoc, eq_comm, 
      inf_eq_right, inf_comm],  
     
    calc x k ≤ (x k ⊔ b) ⊓ (x k ⊔ x (!k))     : le_inf le_sup_left le_sup_left 
        ...  = _ : by {rw [←hsb k, hsb (!k), sup_inf_assoc_of_le, inf_comm, ←h_distrib', sup_comm], 
                        exact le_sup_right}
        ...  ≤ _ : sup_le (sup_le_sup_left inf_le_left _) le_sup_right,
  end, 

  have hs_inf_b : ∀ k, s = ((x k) ⊓ (x (!k))) ⊔ b := 
  λ k, le_antisymm 
    ((hsb k).le.trans (sup_le ((hinf_sup_inf k).le.trans 
      (sup_comm.le.trans (sup_le_sup_left inf_le_right _))) le_sup_right))
    (sup_le ((inf_le_of_left_le (@le_sup_left _ _ (x k) _)).trans (hsb k).symm.le) 
      (le_sup_right.trans (hsb k).symm.le)), 

  rw infi_bool_eq, 
  rw [hs_inf_b tt, bool.bnot_true, hb.sup_canopy_iff_inf_basis], 
  specialize h_can tt, 
  rw [hs_inf_b tt] at h_can, 

  refine indep.basis_of_spans_le (hb.inf_left_indep _) _ inf_le_left,
  have assoc : (x tt ⊓ x ff ⊓ b) = (x tt ⊓ b) ⊓ (x ff ⊓ b) := 
    by {rw [inf_assoc, inf_assoc], congr' 1, simp},
  rw [spans_iff_le_closure, assoc, ←infi_bool_eq, ←@infi_bool_eq _ _ (λ k, (x k ⊓ b)), 
    ←closure_infi_eq_infi_closure_of_indep_bool 
      (hb.indep_of_le (supr_le (λ i, @inf_le_right _ _ (x i) b)))],   

  exact le_infi (λ k, spans_iff_le_closure.mp ((h_bas k).spans.mono_right (infi_le _ _))), 
end 

lemma canopy_for.inf (hsx : s canopy_for x) (hsy : s canopy_for y) : s canopy_for (x ⊓ y) :=
by {convert @canopy_infi_bool _ _ s (λ i, cond i x y) (λ k, by {cases k; assumption}), 
  simp [infi_bool_eq]} 

instance : qmatroid αᵒᵈ := 
{ basis_sup := λ _ _ _, @canopy_for.inf α _ _ _ _,
  basis_Sup_chain := λ _ _ hC, @qmatroid.canopy_Inf_chain _ _ _ _ hC.symm,
  canopy_Inf_chain := λ _ _ hC, @qmatroid.basis_Sup_chain _ _ _ _ hC.symm}

end dual 

lemma canopy_infi_of_forall [nonempty κ] {x : κ → α} (h : ∀ k, s canopy_for (x k)) : 
  s canopy_for (⨅ k, x k) :=
@basis_supr_of_forall αᵒᵈ _ _ _ _ _ h

section minor

open subtype

-- False, even for matroids; the RHS has 'loops
lemma ugh {i a x : α} (hia : i basis_for a) (hax : a ≤ x) : 
  indep (⟨x,hax⟩ : Ici a) ↔ indep (⟨x,hia.le.trans hax⟩ : Ici i) :=
begin
  simp_rw [indep_Ici_iff_exists_canopy_ge_coe, coe_mk], 
  refine ⟨λ h, _, λ h, h.imp (λ t ⟨⟨ht_sp,hat,h_forall⟩, hxt⟩,
    ⟨⟨ht_sp, hax.trans hxt, λ t' ht' hit' ht't, h_forall _ ht' (hia.le.trans hit') ht't⟩, hxt⟩)⟩,
  obtain ⟨t,hta,hxt⟩ := h, 
  obtain ⟨b,hb,rfl,hmin⟩ := hia.exists_base, 
  rw [←hb.sup_canopy_iff_inf_basis] at hia, 

  --have := hia.spanning.ge_canopy_ge_inf, 
  -- obtain ⟨ti, hti⟩ := exists_canopy i, 
  --obtain ⟨t₀,ht₀,ht₀t, htt₀⟩ := --hta.spanning.ge_canopy_ge_inf hti ((hia.le.trans hax).trans hxt),  


  
  --refine ⟨⟨ht_sp,hia.le.trans hat, λ t' ht' hit' ht't, _⟩, hxt⟩,  
  
    
  
    
  

end 

lemma coe_spans_coe_of_spans_Ici {x y : Ici a} (hxy : x spans y) : (x : α) spans y :=
begin
  obtain ⟨⟨x,hxa : a ≤ x⟩,⟨y,hya : a ≤ y⟩⟩ := ⟨x,y⟩, rw [coe_mk,coe_mk], 
  obtain ⟨i,hi⟩ := exists_basis a, 
  obtain ⟨j,hj,hij⟩ := hi.indep.le_basis_of_le (hi.le.trans hxa), 
  rw [spans_iff_forall] at hxy, 
  rw spans_iff_exists, 
  
  -- have : (⟨_, @le_sup_left _ _ a i⟩ : Ici a) basis_for ⟨x,hxa⟩, 
  -- { refine ⟨_,_,_⟩, },
  refine ⟨j, _, hj.le⟩, 
  obtain ⟨b,hb,hjb⟩ := hj.indep, 
  have := (hi.eq_of_le_indep (hb.inf_left_indep a) (le_inf hi.le (hij.trans hjb)) inf_le_left),
  subst this, 
  rw ←hb.sup_canopy_iff_inf_basis at hi, 
  have : (⟨(a ⊔ b) ⊓ x, (le_inf le_sup_left hxa : a ≤ (a ⊔ b) ⊓ x)⟩ : Ici a) basis_for ⟨x,hxa⟩, 
  { refine ⟨_,coe_le_coe.mpr inf_le_right,_⟩, 
    { exact indep_Ici_iff_exists_canopy_ge_coe.mpr ⟨_,hi,inf_le_left⟩},
    rintros ⟨j', (hj' : a ≤ j')⟩ hj' hj'_le hle_j', 
    obtain ⟨t,ht,hj't⟩ := indep_Ici_iff_exists_canopy_ge_coe.mp hj'_1, 
    rw mk_le_mk at hj'_le hle_j', rw coe_mk at hj't, 
    sorry, 
    --have := hj.eq_of_le_indep 
    },

  have := hxy _ this, 


  
   

  
  

end 

end minor


-- lemma closure_infi_eq_infi_closure_of_indep {i : κ → α} (h : indep (⨆ t, i t)) : 
--   (⨅ t, closure (i t)) = closure (⨅ t, i t) :=
-- begin
--   refine (is_empty_or_nonempty κ).elim 
--     (λ h_empty, by simp_rw [@infi_of_empty _ _ _ h_empty, closure_top_eq]) (λ h_ne, _), 
--   obtain ⟨t₀⟩ := h_ne, 
--   refine le_antisymm _ (le_infi (λ t, closure_mono (infi_le _ _))), 
--   rw [←spans_iff_le_closure, spans_iff_exists], 
--   have h_indep := λ t, h.indep_of_le (le_supr _ t), 
--   refine ⟨_, (h.indep_of_le ((infi_le _ t₀).trans (le_supr _ _))).basis_for 
--     le_sup_right (λ k hk hk_le hle_k, hle_k.antisymm _), rfl.le⟩, 


--   rw [sup_eq_left.mpr 
--     (le_infi (λ t, (infi_le _ _).trans (le_closure_self _)) : (⨅ t, i t) ≤ ⨅ t, closure (i t) ), 
--     le_infi_iff] at hk_le,  
--   simp_rw [←spans_iff_le_closure, spans_iff_forall] at hk_le, 
--   have hforall_b := λ t, (hk_le t (i t) (h_indep t).basis_self), clear hk_le, 

--   sorry 

-- end 


end qmatroid
