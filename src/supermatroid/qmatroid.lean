import .supermatroid

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

/-- A `qmatroid` is a `supermatroid` such that, if `i` is a basis for each element in a collection 
`S`, then `i` is a basis for `Sup S`. -/
class qmatroid (α : Type u) extends supermatroid α := 
(basis_for_Sup_of_forall_basis_for : 
  ∀ (i : α) (S : set α) (hS : S.nonempty), (∀ x ∈ S, i basis_for x) → i basis_for (Sup S))

variables [qmatroid α] {S : set α} {i j x y x' y' z z' s t a b : α} {f : α → α}

lemma basis_for_Sup_of_forall (hS : S.nonempty) (h : ∀ x ∈ S, i basis_for x) : 
  i basis_for (Sup S) := 
qmatroid.basis_for_Sup_of_forall_basis_for _ _ hS h 

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


lemma spans_supr_of_forall {a x : κ → α} (h : ∀ k, a k spans x k) : (⨆ k, a k) spans (⨆ k, x k) :=
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
  convert @spans_supr_of_forall α S _ (λ _, a) coe (λ ⟨x,hx⟩, h x hx), 
  rw @supr_const _ _ _ _ hS.to_subtype, simp, 
end 

lemma spans.sup (ha : a spans x) (hb : b spans y) : (a ⊔ b) spans (x ⊔ y) :=
begin
  rw [sup_eq_supr, sup_eq_supr], 
  exact @spans_supr_of_forall _ _ _ (λ i, cond i a b) (λ i, cond i x y) 
    (λ i, by {cases i; assumption}), 
end


lemma basis_for.sup_canopy_of_le_base (hix : i basis_for x) (hb : base b) (hib : i ≤ b) : 
  (x ⊔ b) canopy_for x := 
by {obtain rfl := hix.eq_of_le_indep (hb.inf_left_indep x) (le_inf hix.le hib) inf_le_left, 
  rwa hb.sup_canopy_for_iff_inf_basis_for}


instance : qmatroid αᵒᵈ := { 
   basis_for_Sup_of_forall_basis_for := sorry, 
 }


lemma foo (hsx : s canopy_for x) (hsy : s canopy_for y) : s canopy_for (x ⊓ y) :=

begin
  obtain ⟨b,hb,hbx,hby⟩ := hsx.eq_sup_super_both hsy, 
  --obtain rfl := (by rw [←hbx,←hby, inf_idem]:  s = (x ⊔ b) ⊓ (y ⊔ b)), 
  obtain rfl := (sorry : s = x ⊓ y ⊔ b),  
  
  --simp at hbx hby,    
  
  rw is_modular_lattice.sup_inf_sup_assoc at *, 
  --suffices : (x ⊔ b) ⊓ y ⊔ b canopy_for (x ⊔ b) ⊓ y, 
  --by {refine this.canopy_for_of_le _ (le_inf _ _), }, 
  -- rw [hbx, hb.sup_canopy_for_iff_inf_basis_for] at hsx,
  -- rw [hby, hb.sup_canopy_for_iff_inf_basis_for] at hsy, 
  -- rw hs, 
  
  have hle : (x ⊓ b) ⊔ (y ⊓ b) ≤ (x ⊔ y) ⊓ b := 
    sup_le (inf_le_inf_right _ le_sup_left) (inf_le_inf_right _ le_sup_right),
  
  have hxyb := (hb.inf_left_indep (x ⊔ y)).basis_for_sup_of_spans 
    ((hsx.spans.sup hsy.spans).mono_left hle), 
  rw [sup_inf_self] at hxyb, 
  

  suffices h : (x ⊓ y) ⊔ b canopy_for x ⊓ y, 
  rw [h.eq_of_spanning_le (sorry : _ ≤ s) _ sorry, hb.sup_canopy_for_iff_inf_basis_for], 
  --refine canopy_for.canopy_for_of_le _ _ _, 

  

  

  
  
end 



-- begin
--   obtain ⟨i,hi,hix⟩ := h, 

--   obtain ⟨j,hj,hjx⟩ := hi.indep.le_basis_for_sup_right a, 

--   -- obtain ⟨j',hj',hjj'⟩ := hj.indep.le_basis_for_of_le (sorry : j ≤ x ⊔ a), 
--   -- have := hj.eq_of_le_indep hj'.indep hjj' _, swap, 
  
--   --have : i' ≤ y ⊔ a := by {refine hi'.le.trans _,},
--   --obtain ⟨j,hj,hjy⟩ := hi'.indep.le_basis_for_of_le (sorry : i' ≤ y ⊔ a),
  
--   -- refine ⟨j, hj.indep.basis_for sorry (λ j' hj' hj'y hjj', _), sorry⟩, 
--   -- refine hj.eq_of_le_indep hj' hjj' _, 
  
--   --rw hi.eq_of_le_indep (hj'.inf_right_indep y) sorry inf_le_right, 
-- end 



-- lemma foo (h : ∀ {x y i : α}, i basis_for x → i basis_for y → i basis_for (x ⊔ y)) :
-- (∀ {x y s : α}, s canopy_for x → s canopy_for y → s canopy_for (x ⊓ y)) :=

-- begin
--   rintros x y s hx hy, 
--   obtain ⟨b, hb, hbx, hby⟩ := hx.eq_sup_base_both hy, 
--   refine ⟨⟨b,hb,hbx.substr le_sup_right⟩,inf_le_of_left_le (hbx.substr le_sup_left),
--     λ t ht hxyt hts, le_antisymm (hbx.substr _) hts⟩,  
  
  
-- end 


end qmatroid
