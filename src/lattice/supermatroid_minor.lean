import .supermatroid 

universes u v 

variables {α : Type u} [supermatroid α] {a i s x y b : α}

open subtype set 

section restriction

/-- The restriction of a supermatroid to the elements below a given `a` -/
instance  : supermatroid (Iic a) := { 
  carrier := range (λ (i : {i // i basis_for a}), ⟨i,i.2.le⟩),
  nonempty := exists.elim (exists_basis a) (λ i hi, ⟨⟨i,hi.le⟩,by simpa⟩),
  
  is_antichain :=  
  begin
    rintros ⟨x,hx⟩ ⟨⟨y,hyb⟩,hy⟩ ⟨z,hz⟩ ⟨⟨w,hwb⟩,hw⟩ h_ne h_le, 
    simp only [coe_mk, mk_eq_mk] at hw hy, subst hw, subst hy, 
    exact basis_antichain a hyb hwb (λ hxz, h_ne (mk_eq_mk.mpr hxz)) (mk_le_mk.mp h_le),
  end,
      
  exists_base_mid_of_indep_le_spanning := 
  begin
    rintros ⟨x,hxa⟩ ⟨y,hya⟩ ⟨⟨i,hi⟩,⟨⟨i₀,hi₀b⟩,hi₀⟩,hxi⟩ ⟨⟨i',hi'⟩,⟨⟨i₁,hi₁b⟩,hi₁⟩,hys⟩ hle, 
    simp only [coe_mk, mk_eq_mk] at hi₀ hi₁, subst hi₀, subst hi₁,  
    rw [mk_le_mk] at hle hxi hys, 
    refine (em (x basis_for a)).elim 
      (λ hx, ⟨⟨x, hx.le⟩, ⟨⟨x,hx⟩, by simp only [coe_mk, mk_eq_mk]⟩, by simpa⟩)
      (λ h_nb, _),
  
    obtain ⟨b,hba,hxb,hbx⟩ := 
      ((hi₀b.indep.indep_of_le hxi).lt_basis_le_sup_of_not_basis h_nb hi₁b (hxi.trans hi₀b.le)), 
    
    exact ⟨⟨b,hba.le⟩,⟨⟨b,hba⟩, by simp⟩, by simpa using hxb.le, (hbx.trans (sup_le hle hys))⟩, 
  end,

  le_basis_of_indep_le :=
  begin
    rintros ⟨i,hia⟩ ⟨x,hxa⟩ ⟨⟨i',hi'⟩,⟨⟨i₀,hi₀b⟩,hi₀⟩,hxi'⟩ hix, 
    simp only [coe_mk, mk_eq_mk] at hi₀, subst hi₀, 
    rw [mk_le_mk] at hxi' hix, 
    obtain ⟨j,hj,hij⟩ := (hi₀b.indep.indep_of_le hxi').le_basis_of_le hix, 
    obtain ⟨j',hj',hjj'⟩ := hj.indep.le_basis_of_le (hj.le.trans hxa), 
    refine ⟨⟨j,hj.le.trans hxa⟩, ⟨⟨⟨j',hj'.le⟩,⟨⟨j',hj'⟩,rfl⟩,mk_le_mk.mpr hjj'⟩, 
      mk_le_mk.mpr hj.le, _⟩,
      mk_le_mk.mpr hij⟩, 
    
    rintros ⟨j₁,hj₁a⟩ ⟨⟨b₁, hb₁a⟩,⟨⟨b',hb'⟩,hbb'⟩,hj₁b₁⟩ hj₁x hjj₁, 
    simp only [coe_mk, mk_eq_mk] at hbb' ⊢, subst hbb', rw mk_le_mk at *, 
    exact hj.eq_of_le_indep (hb'.indep_of_le hj₁b₁) hjj₁ hj₁x,
  end,

  .. (infer_instance : complete_lattice (Iic a)) }

@[simp] lemma base_Iic_iff_coe_basis {b : Iic a} : base b ↔ (↑b : α) basis_for a :=
begin
  obtain ⟨b,hba⟩ := b, rw coe_mk, 
  exact ⟨λ ⟨⟨b',hb'⟩,hb⟩, by {simp only [coe_mk, mk_eq_mk] at hb, exact hb ▸ hb'}, 
    λ hb, ⟨⟨b,hb⟩,rfl⟩⟩, 
end 

@[simp] lemma mk_base_iff {a b : α} {hba : b ≤ a} : @base (Iic a) _ ⟨b,hba⟩ ↔ b basis_for a :=
by simp only [base_Iic_iff_coe_basis, coe_mk]

@[simp] lemma indep_Iic_iff_indep {i : Iic a} : indep i ↔ indep (i : α) :=
begin
  obtain ⟨i,hia⟩ := i,
  simp only [@indep_iff_le_base (Iic a), base_Iic_iff_coe_basis, set_coe.exists, mem_Iic, coe_mk, 
    mk_le_mk, exists_prop], 
  exact ⟨λ h, exists.elim h (λ j hj, hj.2.1.indep_of_le hj.2.2), 
    λ h, (h.le_basis_of_le hia).imp (λ j hj, ⟨hj.1.le,hj⟩)⟩, 
end 

@[simp] lemma mk_indep_iff {a i : α} {ha : i ≤ a} : @indep (Iic a) _ ⟨i,ha⟩ ↔ indep i :=
by simp only [indep_Iic_iff_indep, coe_mk]

@[simp] lemma basis_Iic_iff_coe_basis_coe {i x : Iic a} : 
  i basis_for x ↔ (i : α) basis_for (x : α) :=
begin
  obtain ⟨⟨i,hia⟩,⟨x,hxa⟩⟩ := ⟨i,x⟩, 
  simp only [@basis_iff (Iic a), indep_Iic_iff_indep, coe_mk, mk_le_mk, set_coe.forall, mk_eq_mk, 
    mem_Iic], 
  exact ⟨λ ⟨hi,hix,hi'⟩, hi.basis_for hix (λ j hj hjx hij, hi' j (hjx.trans hxa) hj hjx hij), 
    λ h, ⟨h.indep,h.le,λ j hja hj hjx hij, h.eq_of_le_indep hj hij hjx⟩⟩, 
end 

@[simp] lemma mk_basis_iff {a i x : α} {hia : i ≤ a} {hxa : x ≤ a} : 
  (⟨i,hia⟩ : Iic a) basis_for ⟨x,hxa⟩ ↔ i basis_for x := 
by simp only [basis_Iic_iff_coe_basis_coe, coe_mk]

@[simp] lemma spanning_Iic_iff_exists_basis_le_coe {s : Iic a} : 
  spanning s ↔ ∃ i, i basis_for a ∧ i ≤ s :=
begin
  obtain ⟨s,hs⟩ := s, 
  simp only [spanning_iff_basis_le, base_Iic_iff_coe_basis, set_coe.exists, mem_Iic, coe_mk, 
    mk_le_mk, exists_prop], 
  exact ⟨λ h, h.imp (λ i hi, hi.2), λ h, h.imp (λ i hi, ⟨hi.1.le,hi⟩)⟩, 
end  


end restriction

section corestriction

/-- The corestriction of a supermatroid to the elements above a given `a` -/
instance : supermatroid (Ici a) := 
{ carrier := range (λ (s : {s // s canopy_for a}), ⟨s,s.2.le⟩),
  nonempty := exists.elim (exists_canopy a) (λ s hs, ⟨⟨s,hs.le⟩,by simpa⟩),
  
  is_antichain :=  
  begin
    rintros ⟨x,hx⟩ ⟨⟨y,hyb⟩,hy⟩ ⟨z,hz⟩ ⟨⟨w,hwb⟩,hw⟩ h_ne h_le, 
    simp only [coe_mk, mk_eq_mk] at hw hy, subst hy, subst hw, 
    exact canopy_antichain a hyb hwb (λ hxz, h_ne (mk_eq_mk.mpr hxz)) (mk_le_mk.mp h_le),
  end,
      
  exists_base_mid_of_indep_le_spanning := 
    λ i s hi hs his, @spanning.exists_base_mid_of_indep_le (Iic a : set αᵒᵈ) _ s i hi hs his,
  
  le_basis_of_indep_le := λ i x hi hix, @spanning.canopy_le_of_le (Iic a : set αᵒᵈ) _ i x hi hix, 

  .. (infer_instance : complete_lattice (Ici a)) }

lemma base_Ici_iff_coe_canopy {b : Ici a} : 
  base b ↔ (b : α) canopy_for a := 
@base_Iic_iff_coe_basis αᵒᵈ _ _ _

lemma base_Ici_iff_eq_sup_and_inf_basis {s : Ici a} : 
  base s ↔ ∃ b, base b ∧ (s : α) = a ⊔ b ∧ a ⊓ b basis_for a :=
begin
  obtain ⟨s,(hs : a ≤ s)⟩ := s, 
  rw [base_Ici_iff_coe_canopy, coe_mk], 
  refine ⟨λ h, _, by {rintros ⟨_,h,rfl,_⟩, rwa h.sup_canopy_iff_inf_basis}⟩,
  obtain ⟨b, hb, rfl ,h'⟩ := h.exists_base, 
  exact ⟨_,hb,rfl,hb.sup_canopy_iff_inf_basis.mp h⟩, 
end 

lemma base.sup_base_Ici_iff (hb : base b) : 
  base (⟨a ⊔ b, @le_sup_left _ _ a b⟩ : Ici a) ↔ a ⊓ b basis_for a := 
by rw [base_Ici_iff_coe_canopy, coe_mk, hb.sup_canopy_iff_inf_basis]

lemma base.sup_base_Ici_of_inf_basis (hb : base b) (hab : a ⊓ b basis_for a):
  base (⟨a ⊔ b, @le_sup_left _ _ a b⟩ : Ici a) := 
hb.sup_base_Ici_iff.mpr hab 

lemma indep_Ici_iff_exists_canopy_ge_coe {s : Ici a} :
  indep s ↔ ∃ t, t canopy_for a ∧ (s : α) ≤ t := 
@spanning_Iic_iff_exists_basis_le_coe αᵒᵈ _ _ s

lemma indep_Ici_iff_coe_le_sup_base {i : Ici a} : 
  indep i ↔ ∃ b, base b ∧ (a ⊓ b) basis_for a ∧ (i : α) ≤ a ⊔ b := 
begin
  rw indep_Ici_iff_exists_canopy_ge_coe, 
  split, 
  { rintros ⟨t,hta,hit⟩, 
    obtain ⟨b,hb,rfl,hmin⟩ := hta.exists_base, 
    exact ⟨_, hb, hb.sup_canopy_iff_inf_basis.mp hta, hit⟩},
  rintros ⟨b,hb,hab,hiab⟩, 
  refine ⟨_, hb.sup_canopy_iff_inf_basis.mpr hab, hiab⟩, 
end 

lemma foo_Ici {i x : α} (hix : i basis_for x) : 
  ∃ (j : Ici a), (j :α) ≤ a ⊔ i ∧ j basis_for ⟨a ⊔ x, (le_sup_left : a ≤ a ⊔ x)⟩ :=
begin
  obtain ⟨⟨k,(hak : a ≤ k)⟩,hk⟩ := exists_basis (⟨a ⊔ i, (le_sup_left : a ≤ a ⊔ i)⟩ : Ici a), 
  refine ⟨⟨k,hak⟩,hk.le, hk.indep, mk_le_mk.mpr (le_trans hk.le (sup_le_sup_left hix.le _)),_⟩, 
  rintros ⟨j,(hja : a ≤ j)⟩ hji hjax hkj, 
  refine hk.eq_of_le_indep hji hkj (mk_le_mk.mpr _), 
  
  --obtain ⟨b,hb,hab,hjab⟩ := indep_Ici_iff_coe_le_sup_base.mp hji, 

  --rw mk_le_mk at *, rw mk_eq_mk, 
  
  --rintros ⟨⟨j,(hja : a ≤ j)⟩, _⟩, 

end 

-- lemma basis_Ici_iff {i x : Ici a} : 
--   i basis_for x ↔ ∃ b, base b ∧ (a ⊓ b) basis_for a ∧ (i :α) = x ⊓ (a ⊔ b) ∧ 
--     ∀ b', base b' → (a ⊓ b') basis_for a → a ⊓ b ≤ b' → a ⊓ b = a ⊓ b' := 
-- begin
  
--   obtain ⟨⟨i, (hai : a ≤ i)⟩,⟨x, (hax : a ≤ x)⟩⟩ := ⟨i,x⟩, 
  
   
--   simp_rw coe_mk at *, 
--   refine ⟨λ h, _, λ h, _⟩, 
--   { obtain ⟨⟨s,h₀⟩,hs, hixs, hforall⟩ := h.exists_base, 
--     rw [base_Ici_iff_coe_canopy, coe_mk] at hs, 
--     obtain ⟨b,hb,rfl,hmax⟩ := hs.exists_base, 
--     simp only [subtype.mk_sup, subtype.mk_inf, mk_eq_mk] at *, 
--     subst hixs,
--     rw hb.sup_canopy_iff_inf_basis at hs, 
--     refine ⟨b,hb,hs,rfl,λ b' hb' hab' hb'b, _⟩, 
    
--     have := hforall _ (hb'.sup_base_Ici_of_inf_basis hab') 
--       (mk_le_mk.mpr (by {rw [inf_comm, sup_inf_assoc_of_le _ hax, inf_comm], 
--         refine sup_le le_sup_left _, 
--         have := hab'.eq_of_le_indep (hb.inf_left_indep x) sorry, 
--          })), 
    

    
    
--      },
  
--   -- { rintros ⟨⟨b,hb,hab,hiab⟩,hix, hmax⟩,  
--   --   simp_rw coe_mk at *, 
--   --   refine ⟨b, hb, hab, (le_inf (mk_le_mk.mp hix) hiab).antisymm _, _⟩, 
     
--   --   { },
  
-- end 
  

-- lemma foo {a : α} {i x : Iic a} {j : α} (hix : i basis_for x) (hji : j basis_for i) 
-- (haj : a ⊓ j basis_for a) : j basis_for x := 
-- begin
--   obtain ⟨⟨i,hia⟩,⟨x,hxa⟩⟩ := ⟨i,x⟩, 
--   rw [coe_mk] at *, 
--   refine hji.indep.basis_for (hji.le.trans (coe_le_coe.mpr hix.le)) (λ j' hj' hj'x hjj', _), 
  
  
-- end 

end corestriction
