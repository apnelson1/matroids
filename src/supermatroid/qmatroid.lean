import .supermatroid 
import order.zorn

universes u v 

open set 

variables {α : Type u} {κ : Type v}

section defs

variables [base_family α] {i x y : α}

/-- `x` spans `y` if every base for `x` is a base for `y ⊔ x` -/
def spans (x y : α) := ∀ i, i basis_for x → i basis_for (y ⊔ x)

infix ` spans `:50 := spans

def closure (x : α) : α := Sup {y | ∀ i, i basis_for x → i basis_for (y ⊔ x)}

lemma spans.basis_for (hxy : x spans y) (hix : i basis_for x) : i basis_for (y ⊔ x) := hxy _ hix 

lemma spans_iff_forall : (x spans y) ↔ ∀ i, i basis_for x → i basis_for (y ⊔ x) := iff.rfl 

end defs

section qmatroid 

/-- A `qmatroid` is a `supermatroid` with some lattice-closure conditions on the set of elements
spanned by an independent set i -/
class qmatroid (α : Type u) extends supermatroid α := 
(basis_for_sup : ∀ (i x y : α), i basis_for x → i basis_for y → i basis_for x ⊔ y)
(basis_for_Sup_chain : ∀ (i C), 
  is_chain (≤) C → C.nonempty → (∀ (x ∈ C), i basis_for x) → i basis_for (Sup C))
(canopy_for_Inf_chain : ∀ (s C), 
  is_chain (≤) C → C.nonempty → (∀ (x ∈ C), s canopy_for x) → s canopy_for (Inf C))

variables [qmatroid α] {S : set α} {i j x y x' y' z z' s t a b : α} {f : α → α}

lemma basis_for.sup (hx : i basis_for x) (hy : i basis_for y) : i basis_for x ⊔ y := 
qmatroid.basis_for_sup _ _ _ hx hy 

lemma indep.basis_for_Sup_basis_for (hi : indep i) : i basis_for Sup {x | i basis_for x} :=
begin
  obtain ⟨u, hub, hu⟩ := @zorn_partial_order₀ α _ {x | i basis_for x} 
    (λ C hCb hC, C.eq_empty_or_nonempty.elim 
      (by {rintro rfl, exact ⟨i, hi.basis_for_self, by simp⟩, })
      (λ hC_ne, ⟨Sup C, qmatroid.basis_for_Sup_chain _ _ hC hC_ne hCb, λ _, le_Sup⟩)), 
  rwa (le_Sup hub).antisymm'   
    (Sup_le (λ x hx, sup_eq_right.mp (hu _ (basis_for.sup hx hub) le_sup_right))), 
end 

lemma basis_for_Sup_of_forall (hS : S.nonempty) (h : ∀ x ∈ S, i basis_for x) : 
  i basis_for (Sup S) := 
(exists.elim hS (λ x hx, (h x hx).indep)).basis_for_Sup_basis_for.basis_for_of_le 
  (exists.elim hS (λ x hx, (h x hx).le.trans (le_Sup hx)))
  (Sup_le (λ x hx, le_Sup (h x hx)))

lemma basis_for_bsupr_of_forall (hS : S.nonempty) (h : ∀ x ∈ S, i basis_for (f x)) : 
  i basis_for (⨆ (x ∈ S), f x) :=
by {rw ←Sup_image, exact basis_for_Sup_of_forall (hS.image _) (λ x ⟨y,hy,hyx⟩, 
      by {rw ← hyx, exact h _ hy})}

lemma basis_for_supr_of_forall [nonempty κ] {x : κ → α} (h : ∀ k, i basis_for (x k)) :
  i basis_for (⨆ k, x k) :=
basis_for_Sup_of_forall (range_nonempty x) (λ y ⟨k,hk⟩,hk.subst (h k))

lemma basis_for_Sup_of_forall_sup (hS : S.nonempty) (h : ∀ x ∈ S, i basis_for (x ⊔ i)) : 
  i basis_for (Sup S ⊔ i) := 
by {rw [Sup_eq_supr, ←bsupr_sup hS], exact basis_for_bsupr_of_forall hS h} 
  
lemma indep.basis_for_Sup_of_forall_sup (hi : indep i) (h : ∀ x ∈ S, i basis_for x ⊔ i) : 
  i basis_for (Sup S) ⊔ i := 
S.eq_empty_or_nonempty.elim (by {rintro rfl, simpa using hi.basis_for_self}) 
  (λ hS, basis_for_Sup_of_forall_sup hS h)

lemma basis_for.basis_for_sup_of_basis_for (hx : i basis_for x) (hy : i basis_for y) : 
  i basis_for (x ⊔ y) := 
by {rw sup_eq_supr, exact basis_for_supr_of_forall (λ k, by {cases k; assumption})}

lemma le_closure_self (x : α) : x ≤ closure x := le_Sup (by simp)

lemma indep.basis_for_closure (hi : indep i) : i basis_for (closure i) := 
begin
  rw [←sup_eq_left.mpr (le_closure_self i)], 
  exact basis_for_Sup_of_forall_sup ⟨i, by simp⟩ (λ x hx, hx i hi.basis_for_self),
end 

lemma basis_for.basis_for_closure (hix : i basis_for x) : i basis_for (closure x) :=
begin
  rw [←sup_eq_left.mpr (hix.le.trans (le_closure_self x))], 
  refine basis_for_Sup_of_forall_sup ⟨x, by simp⟩ (λ y hy, _), 
  exact (hy _ hix).basis_for_of_le le_sup_right (sup_le_sup_left hix.le _), 
end 

lemma indep.basis_for_sup_of_le_closure (hi : indep i) (hxi : x ≤ closure i) : 
  i basis_for (i ⊔ x) :=
hi.basis_for_closure.basis_for_of_le le_sup_left (sup_le (le_closure_self i) hxi)

lemma spans_closure_self (x : α) : x spans (closure x) := 
begin
  rintros i hi, 
  rw [sup_eq_left.mpr (le_closure_self x), ←sup_eq_left.mpr (hi.le.trans (le_closure_self x))], 
  exact hi.indep.basis_for_Sup_of_forall_sup 
    (λ y hy, (hy i hi).basis_for_of_le le_sup_right (sup_le_sup_left hi.le _)), 
end

lemma basis_for.basis_for_of_basis_for_basis_for_le (hix : i basis_for x) (hiy : i basis_for y)
(hjx : j basis_for x) (hjy : j ≤ y) :
  j basis_for y :=
begin
  obtain ⟨j',hj',hjj'⟩ := hjx.indep.le_basis_for_of_le hjy,
  refine hjj'.lt_or_eq.elim (λ hlt, by_contra (λ hjy', _)) (λ h, h.substr hj'), 
  obtain ⟨k,hk,hjk,hki⟩ := hjx.indep.lt_basis_for_le_sup_of_not_basis_for hjy' hiy hjy, 
  exact hjx.not_indep_of_lt hjk (hki.trans (sup_le hjx.le hix.le)) hk.indep, 
end 

lemma basis_for.basis_for_sup_of_le_closure (hix : i basis_for x) (hyx : y ≤ closure x) : 
  i basis_for (y ⊔ i) :=
((spans_closure_self x).basis_for hix).basis_for_of_le le_sup_right (sup_le_sup hyx hix.le)
 
lemma basis_for.spans_iff_basis_for_sup (hi : i basis_for x) : 
  x spans y ↔ i basis_for (y ⊔ i) :=
begin
  refine ⟨λ h, (h _ hi).basis_for_of_le le_sup_right (sup_le_sup_left hi.le _), λ h j hj, _⟩,
  refine (hi.basis_for_of_basis_for_basis_for_le (hi.basis_for_sup_of_basis_for h) hj 
    (hj.le.trans le_sup_left)).basis_for_of_le 
    (hj.le.trans le_sup_right) (by {rw sup_comm, exact sup_le_sup_left le_sup_left _}), 
end 

lemma basis_for.le_closure_iff_basis_for_sup (hix : i basis_for x): 
  y ≤ closure x ↔ i basis_for (y ⊔ i)  :=
begin
  refine ⟨hix.basis_for_sup_of_le_closure,λ h, le_Sup (λ j hj, _)⟩, 
  exact (hix.basis_for_of_basis_for_basis_for_le (hix.basis_for_sup_of_basis_for h) hj 
    (hj.le.trans le_sup_left)).basis_for_of_le 
    (hj.le.trans le_sup_right) (by {rw sup_comm, exact sup_le_sup_left le_sup_left _}), 
end 

lemma spans_iff_le_closure : 
  x spans y ↔ y ≤ closure x :=
by {obtain ⟨i,hi⟩ := exists_basis_for x, 
  rw [hi.le_closure_iff_basis_for_sup, hi.spans_iff_basis_for_sup]}

lemma basis_for.spans_of_basis_for_sup (hix : i basis_for x) (hiy : i basis_for (y ⊔ i)) :
  x spans y := 
hix.spans_iff_basis_for_sup.mpr hiy 

lemma spans.mono_right (hxy : x spans y) (hy'y : y' ≤ y) : x spans y' :=
λ i hix, (hxy _ hix).basis_for_of_le (le_sup_of_le_right hix.le) (sup_le_sup_right hy'y _)
 
lemma spans.mono_left (hxy : x spans y) (hxx' : x ≤ x') : x' spans y :=
begin
  obtain ⟨i,hi⟩ := exists_basis_for x, 
  obtain ⟨i',hi',hii'⟩ := hi.indep.le_basis_for_of_le (hi.le.trans hxx'),
  exact hi'.spans_of_basis_for_sup 
   (((hxy.basis_for hi).basis_for_sup_mono hi'.indep hii').basis_for_of_le le_sup_right 
    (sup_le_sup_right le_sup_left _)), 
end 

lemma spans.mono (hxy : x spans y) (hxx' : x ≤ x') (hy'y : y' ≤ y) : x' spans y' :=
(hxy.mono_left hxx').mono_right hy'y

lemma spans_bot (x : α) : x spans ⊥ := λ i hi, by rwa bot_sup_eq

lemma spans_iff_exists : 
  x spans y ↔ ∃ i, i basis_for (y ⊔ i) ∧ i ≤ x :=
⟨λ h, (exists_basis_for x).imp (λ i hi, ⟨hi.spans_iff_basis_for_sup.mp h,hi.le⟩), 
  λ ⟨i, hi, hix⟩, spans.mono_left (hi.indep.basis_for_self.spans_of_basis_for_sup hi) hix⟩

lemma basis_for.spans_of_basis_for (hi : i basis_for x) (hiy : i basis_for (y ⊔ i)) : x spans y :=
  spans_iff_exists.mpr ⟨i, hiy, hi.le⟩ 

lemma basis_for.spans (hi : i basis_for x) : i spans x := 
spans_iff_exists.mpr ⟨i, hi.basis_for_sup_self, rfl.le⟩ 

lemma basis_for.spans_right (hi : i basis_for x) : x spans i := 
spans_iff_exists.mpr ⟨i , sup_idem.substr hi.indep.basis_for_self, hi.le⟩
  
lemma indep.basis_for_sup_of_spans (hi : indep i) (hix : i spans x) : i basis_for x ⊔ i := 
begin
  obtain ⟨i',hi',hi'i⟩ := spans_iff_exists.mp hix, 
  refine (hi'.basis_for_sup_mono hi hi'i).basis_for_of_le le_sup_right _,
  rw sup_right_comm, exact le_sup_left, 
end 

lemma indep.basis_for_of_spans_le (hi : indep i) (hix : i spans x) (hle : i ≤ x) : i basis_for x := 
(sup_eq_left.mpr hle) ▸ (hi.basis_for_sup_of_spans hix)

lemma closure_idem (x : α) : closure (closure x) = closure x :=
begin
  refine le_antisymm _ (le_closure_self _), 
  obtain ⟨i,hi⟩ := exists_basis_for x, 
  rw [hi.le_closure_iff_basis_for_sup, 
    sup_eq_left.mpr (hi.le.trans ((le_closure_self x).trans (le_closure_self _)))],
  exact basis_for.basis_for_closure (basis_for.basis_for_closure hi), 
end 

lemma indep.inf_Sup_basis_for_Sup_of_forall_inf_basis_for (hi : indep i)
(hS : ∀ x ∈ S, (x ⊓ i) basis_for x) : 
  (Sup S ⊓ i) basis_for (Sup S) :=
begin
  refine S.eq_empty_or_nonempty.elim (by {rintro rfl, simpa using (bot_indep α).basis_for_self}) 
    (λ hS_ne, _), 
  
  obtain ⟨k,hk,hkS⟩ := (hi.inf_left_indep (Sup S)).le_basis_for_of_le inf_le_left, 
  have hxS := λ {x : α} (hx : x ∈ S), (hS x hx).eq_of_le_indep (hk.indep.inf_left_indep x) 
    (le_inf inf_le_left (le_trans (inf_le_inf_right _ (le_Sup hx)) hkS)) inf_le_left,   
  
  have hb := λ x hx, (hS x hx).basis_for_sup_mono (hi.inf_left_indep (Sup S))
    (inf_le_inf_right i (le_Sup hx)), 
  refine (basis_for_bsupr_of_forall hS_ne hb).basis_for_of_le inf_le_left _,  
  rw ←Sup_image, 
  refine Sup_le_Sup_of_forall_exists_le (λ x hx, _), 
  simp only [mem_image, exists_prop, exists_exists_and_eq_and], 
  refine ⟨x,hx, le_sup_left⟩,
end 

lemma supr_basis_for_supr_of_forall {κ : Type v} {i x : κ → α} 
(h : ∀ k, (i k) basis_for (x k)) (hind : indep (⨆ k, (i k))) : 
  (⨆ k, i k) basis_for (⨆ k, x k) :=
begin
  refine hind.basis_for (supr_le (λ k, (h k).le.trans (le_supr _ _))) (λ j hj hjle hi'j, _), 
  set i' := ⨆ k, i k with hi', 
  have h' : ∀ k, (i k) = (x k)  ⊓ i' := λ k, (h k).eq_of_le_indep 
    (hind.inf_left_indep _) (le_inf (h k).le (le_supr _ _) ) inf_le_left,
  simp_rw h' at h, 
  have hb := @indep.inf_Sup_basis_for_Sup_of_forall_inf_basis_for _ _ (range x) _ hind
    (λ y ⟨z,hz⟩, by {simpa [hz] using h z}),  
  obtain rfl := hb.eq_of_le_indep hj (le_trans inf_le_right hi'j) hjle, 
  exact hi'j.antisymm inf_le_right, 
end 


lemma basis_for.baz (hi : i basis_for x) (hj : j basis_for y) (hij : indep (i ⊔ j)) : 
  (i ⊔ j) basis_for (x ⊔ y) :=
begin
  have := @supr_basis_for_supr_of_forall _ _ _ (λ b, cond b i j) (λ b, cond b x y) 
    (λ k, by {cases k; simpa}), 
  simp only [supr_bool_eq] at this, 
  exact this hij, 
end 

lemma basis_for.baz' (hi : i basis_for x) (hj : j basis_for y) (hij : i ≤ j) : 
  j basis_for (x ⊔ y) :=
let hij' := sup_eq_right.mpr hij in by {convert hi.baz hj (by {rw hij', exact hj.indep}), rw hij'} 

lemma closure_mono (hxy : x ≤ y) : closure x ≤ closure y :=
begin
  obtain ⟨i,hi⟩ := exists_basis_for x, 
  obtain ⟨j, hj, hij⟩ := hi.indep.le_basis_for_of_le (hi.le.trans hxy), 
  exact hj.le_closure_iff_basis_for_sup.mpr  
    (basis_for_Sup_of_forall_sup (⟨x, λ hk, by {rw sup_idem, exact id}⟩) 
      (λ z hz, ((hz _ hi).baz' hj hij).basis_for_of_le le_sup_right 
        (sup_assoc.substr (sup_le_sup_left (le_sup_of_le_right hj.le) _)))), 
end 

lemma spans.trans (hxy : x spans y) (hyz : y spans z) : x spans z :=
begin
  obtain ⟨i,hi⟩ := exists_basis_for x, 
  refine basis_for.spans_of_basis_for_sup hi _, 
  have hb := (hxy.basis_for hi).basis_for_of_le le_sup_right (sup_le_sup_left hi.le y),  
  exact ((hyz.mono_left le_sup_left) i hb).basis_for_of_le le_sup_right 
    (sup_le_sup_left le_sup_right _), 
end 


lemma supr_spans_supr_of_forall {a x : κ → α} (h : ∀ k, a k spans x k) : (⨆ k, a k) spans (⨆ k, x k) :=
begin
  refine (is_empty_or_nonempty κ).elim (λ he, _ ) (λ hk, _),
  { simp_rw @supr_of_empty _ _ _ he, exact spans_bot _, },
  obtain ⟨i, hi⟩ := exists_basis_for (⨆ k, a k),  
  have h1 := λ k, (hi.spans.mono_right (le_supr _ _)).trans (h k), 
  have h2 := (λ k, hi.indep.basis_for_sup_of_spans (h1 k)),  
  have h3 := (@basis_for_supr_of_forall α _ _ _ hk _ h2).spans,  
  refine (hi.spans_right.trans h3).mono_right _, 
  rw [←(@supr_sup _ _ _ hk)], exact le_sup_left, 
end 

lemma spans_Sup_of_forall (h : ∀ x ∈ S, a spans x) : a spans (Sup S) :=
begin
  refine S.eq_empty_or_nonempty.elim (by {rintro rfl, simpa using spans_bot _}) (λ hS, _),
  convert @supr_spans_supr_of_forall α S _ (λ _, a) coe (λ ⟨x,hx⟩, h x hx), 
  rw @supr_const _ _ _ hS.to_subtype, simp, 
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
  rwa hb.sup_canopy_for_iff_inf_basis_for}

lemma closure_inf_eq_inf_closure_of_indep (hij : indep (i ⊔ j)) : 
  closure i ⊓ closure j = closure (i ⊓ j) :=
begin
  refine le_antisymm _ (le_inf (closure_mono inf_le_left) (closure_mono inf_le_right)),
  rw [←spans_iff_le_closure, spans_iff_exists], 
  obtain ⟨hi,hj⟩  := ⟨hij.indep_of_le le_sup_left, hij.indep_of_le le_sup_right⟩, 
  refine ⟨i ⊓ j, (hij.indep_of_le inf_le_sup).basis_for le_sup_right _, rfl.le⟩,
  intros k hk hkij hijk, 
  rw [sup_eq_left.mpr _] at hkij, swap, exact inf_le_inf (le_closure_self _) (le_closure_self _),
  obtain ⟨hki,hkj⟩ := le_inf_iff.mp hkij, 
  rw [←spans_iff_le_closure, spans_iff_forall] at hki hkj, 
  specialize hkj _ (hj.basis_for_self), 
  specialize hki _ (hi.basis_for_self), 
  clear hkij, 

  --- Hmm.... ideas:
  --- WMA i ⊔ j is a basis (otherwise restrict to i ⊔ j) ...
  --- and (probably) that i ⊓ j = ⊥ (otherwise contract i ⊓ j)
  --- extend k to bases ki and kj of i ⊔ k and j ⊔ k respectively. 
  --- By hkj and hij, the elements i ⊔ kj, j ⊔ ki and (ki ⊔ kj) are spanning. 
  --- Since i is a basis of i ⊔ k, (i ⊔ j) ⊔ (i ⊔ k) = i ⊔ j ⊔ k is a canopy of i ⊔ k. 
  --- It follows that i ⊔ kj = i ⊔ j ⊔ k, since i ⊔ kj is a spanning set in [i ⊔ k, i ⊔ j ⊔ k]. 
  --- Similarly, j ⊔ ki = i ⊔ j ⊔ k. 
  --- It follows that all the elements in [ki, i ⊔ j ⊔ k] have the same sup with j. 
  --- Try to find two that have the same inf! Or to exploit symmetry or something...  so close. 
  
    
end  


lemma Foo {x : bool → α} (h_can : ∀ k, s canopy_for (x k)) : s canopy_for (⨅ k, x k) :=
begin
  obtain ⟨b,hb, (hsb : ∀ k, s = x k ⊔ b)⟩ := eq_sup_basis_forall_of_canopy_for_forall h_can, 

  have h_bas := λ k, hb.sup_canopy_for_iff_inf_basis_for.mp ((hsb k).subst (h_can k)),

  have hsupr_inf_basis : (⨆ k, ((x k) ⊓ b)) basis_for ⨆ k, x k := indep.basis_for_of_spans_le 
    (hb.indep_of_le (Sup_le (by simp)))
    (supr_spans_supr_of_forall (λ k, (h_bas k).spans))
    (supr_le (λ k, inf_le_left.trans (le_supr _ _))),
    
  have h_distrib : (⨆ k, x k ⊓ b) = (⨆ k, x k) ⊓ b := 
    hsupr_inf_basis.eq_of_le_indep (hb.inf_left_indep _) 
    (supr_le (λ k, inf_le_inf_right _ (le_supr _ _))) inf_le_left,  

  have h_distrib' : ∀ k, (x k ⊓ b) ⊔ (x (!k)) ⊓ b = (x k ⊔ x (!k)) ⊓ b :=   
    λ k, by rw [←supr_bool_eq' k, h_distrib, supr_bool_eq'],

  have hwow : ∀ k, x k = (x k) ⊓ b ⊔ ((x k) ⊓ (x (!k))) := 
  begin
    intro k, 
    rw [inf_comm, @inf_comm _ _ _ (x (!k)), is_modular_lattice.inf_sup_inf_assoc, eq_comm, 
      inf_eq_right, inf_comm],  
     
    calc x k ≤ (x k ⊔ b) ⊓ (x k ⊔ x (!k))     : le_inf le_sup_left le_sup_left 
        ...  = _ : by {rw [←hsb k, hsb (!k), sup_inf_assoc_of_le, inf_comm, ←h_distrib', sup_comm], 
                        exact le_sup_right}
        ...  ≤ _ : sup_le (sup_le_sup_left inf_le_left _) le_sup_right,
  end, 

  have hwoww : ∀ k, s = ((x k) ⊓ (x (!k))) ⊔ b := 
  λ k, le_antisymm 
    ((hsb k).le.trans (sup_le ((hwow k).le.trans 
      (sup_comm.le.trans (sup_le_sup_left inf_le_right _))) le_sup_right))
    (sup_le ((inf_le_of_left_le (@le_sup_left _ _ (x k) _)).trans (hsb k).symm.le) 
      (le_sup_right.trans (hsb k).symm.le)), 

  rw infi_bool_eq, 
  rw [hwoww tt, bool.bnot_true, hb.sup_canopy_for_iff_inf_basis_for], 
  specialize h_can tt, 
  rw [hwoww tt] at h_can, 

  refine indep.basis_for_of_spans_le (hb.inf_left_indep _) _ inf_le_left,
  have blah : (x tt ⊓ x ff ⊓ b) = (x tt ⊓ b) ⊓ (x ff ⊓ b) := 
    by {rw [inf_assoc, inf_assoc], congr' 1, simp},
  rw [spans_iff_le_closure, blah, 
    ←closure_inf_eq_inf_closure_of_indep (hb.indep_of_le (sup_le inf_le_right inf_le_right))],   
  
  exact inf_le_inf (spans_iff_le_closure.mp ((h_bas _).spans)) 
    (spans_iff_le_closure.mp ((h_bas _).spans)),   
end 


lemma foo (hsx : s canopy_for x) (hsy : s canopy_for y) : s canopy_for (x ⊓ y) :=

begin
  --rw [cheat, canopy_for_bot_iff], 
  obtain ⟨b,hb,hsbx,hsby⟩ := hsx.eq_sup_super_both hsy, 
  --obtain rfl := (by rw [←hbx,←hby, inf_idem]:  s = (x ⊔ b) ⊓ (y ⊔ b)), 
  --obtain rfl := (sorry : s = x ⊓ y ⊔ b),  
  
  
  --simp at hbx hby,    
  rw hsbx at hsx, rw hsby at hsy, 
  
  have hbx := hb.sup_canopy_for_iff_inf_basis_for.mp hsx, 
  have hby := hb.sup_canopy_for_iff_inf_basis_for.mp hsy, 
  --rw is_modular_lattice.sup_inf_sup_assoc at *, 
  --suffices : (x ⊔ b) ⊓ y ⊔ b canopy_for (x ⊔ b) ⊓ y, 
  --by {refine this.canopy_for_of_le _ (le_inf _ _), }, 
  -- rw [hbx, hb.sup_canopy_for_iff_inf_basis_for] at hsx,
  -- rw [hby, hb.sup_canopy_for_iff_inf_basis_for] at hsy,
  have hxy : (x ⊔ y) ⊓ b basis_for x ⊔ y :=
  begin
    refine (hb.inf_left_indep _).basis_for_of_spans_le _ inf_le_left, 
    exact (hbx.spans.sup hby.spans).mono_left 
      (sup_le (inf_le_inf_right _ le_sup_left) (inf_le_inf_right _ le_sup_right)), 
  end,

  have hxy' := 
  indep.basis_for_of_spans_le (hb.indep_of_le (sup_le inf_le_right inf_le_right)) 
    (hbx.spans.sup hby.spans) 
      (sup_le (inf_le_of_left_le le_sup_left) (inf_le_of_left_le le_sup_right)), 
  
  by_contradiction hs, 
  obtain ⟨b',hb',hb'xy, hb's⟩ := (sorry : spanning s).exists_sup_base_lt_of_not_canopy_for hs sorry,

  have hb'i := hb'.sup_canopy_for_iff_inf_basis_for.mp hb'xy, 

  have hb'x : b' < x ⊔ b := ((sup_le_iff.mp hb's.le).2.trans hsbx.le).lt_of_ne 
    (λ h, hb's.not_le (hsbx.le.trans (h ▸ le_sup_right))), 
  
  -- have hb'y : b' < y ⊔ b := ((sup_le_iff.mp hb's.le).2.trans hsby.le).lt_of_ne 
  --   (λ h, hb's.not_le (hsby.le.trans (h ▸ le_sup_right))), 
  
  have : x ⊔ b' = x ⊔ b :=
    hsx.eq_of_spanning_le le_sup_left (sup_le le_sup_left hb'x.le) (hb'.sup_left_spanning _), 
  
  
  

  


  
end 

  

  

  

  -- obtain ⟨i,hi,hlei⟩ := (hb.inf_left_indep x).le_basis_for_sup_right y, 
  
  -- obtain ⟨b',hb',hib',hb'i⟩ := hi.indep.exists_base_mid_of_le_sup_base hb, 
  -- have h' := hsy.eq_of_spanning_le le_sup_left (sup_le le_sup_left _) (hb'.sup_left_spanning _), 
  -- swap, 
  -- { refine hb'i.trans (sup_le (hi.le.trans _) le_sup_right), 
  --   rw sup_comm, exact (sup_le_sup_left inf_le_right _)},

  

  -- have := @eq_of_le_of_inf_le_of_sup_le' _ _ _ (x ⊓ b) x y inf_le_left (by {rw cheat, exact bot_le})
  --   (calc x ≤ (x ⊔ b)           : le_sup_left 
  --       ... = (y ⊔ b')          : by {rw [←hsbx, hsby, h']} 
  --       ... ≤ (y ⊔ (x ⊓ b ⊔ y)) : sup_le_sup_left hi.le _
  --       ... = ((x ⊓ b) ⊔ y)     : by {rw [sup_left_comm, sup_idem]}),





  
  






--   -- obtain ⟨iy, hiy, hyiy⟩ := (hb.inf_left_indep y).le_basis_for_sup_right x,
--   -- obtain ⟨ix, hix, hxix⟩ := (hb.inf_left_indep x).le_basis_for_sup_right y,

--   -- have : ix ⊓ x ≤ b, sorry, 



--   --rw ←hb.sup_canopy_for_iff_inf_basis_for at hxy, 
  

--   -- -- rw hs, 
  
--   -- have hle : (x ⊓ b) ⊔ (y ⊓ b) ≤ (x ⊔ y) ⊓ b := 
--   --   sup_le (inf_le_inf_right _ le_sup_left) (inf_le_inf_right _ le_sup_right),
  
--   -- have hxyb := (hb.inf_left_indep (x ⊔ y)).basis_for_sup_of_spans 
--   --   ((hsx.spans.sup hsy.spans).mono_left hle), 
--   -- rw [sup_inf_self] at hxyb, 
  

--   -- suffices h : (x ⊓ y) ⊔ b canopy_for x ⊓ y, 
--   -- rw [h.eq_of_spanning_le (sorry : _ ≤ s) _ sorry, hb.sup_canopy_for_iff_inf_basis_for], 
--   -- --refine canopy_for.canopy_for_of_le _ _ _, 

  

  

  
  
-- end 



-- -- begin
-- --   obtain ⟨i,hi,hix⟩ := h, 

-- --   obtain ⟨j,hj,hjx⟩ := hi.indep.le_basis_for_sup_right a, 

-- --   -- obtain ⟨j',hj',hjj'⟩ := hj.indep.le_basis_for_of_le (sorry : j ≤ x ⊔ a), 
-- --   -- have := hj.eq_of_le_indep hj'.indep hjj' _, swap, 
  
-- --   --have : i' ≤ y ⊔ a := by {refine hi'.le.trans _,},
-- --   --obtain ⟨j,hj,hjy⟩ := hi'.indep.le_basis_for_of_le (sorry : i' ≤ y ⊔ a),
  
-- --   -- refine ⟨j, hj.indep.basis_for sorry (λ j' hj' hj'y hjj', _), sorry⟩, 
-- --   -- refine hj.eq_of_le_indep hj' hjj' _, 
  
-- --   --rw hi.eq_of_le_indep (hj'.inf_right_indep y) sorry inf_le_right, 
-- -- end 


end qmatroid
