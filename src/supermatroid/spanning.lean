
import .basic 

universes u v

variables {α : Type u} [lattice α] [is_modular_lattice α] [bounded_order α] 
  {M : supermatroid α} {i j b x y c d r : α}

namespace supermatroid

lemma something (x : α) (hb : M.basis b) : 
  ∃ b', M.basis b' ∧ b ≤ b' ⊔ x ∧ ∀ b'', M.basis b'' → b' ≤ b'' ⊔ x → b' ⊔ x = b'' ⊔ x := 
begin
  obtain ⟨b',hb'x, hb', hb'1⟩ := hb.exists_extension_from x,
  by_contradiction h,
  push_neg at h, 
  obtain ⟨b'', bh'',hbb'', hb''b⟩ :=  h b hb le_sup_left, 
end 


-- lemma foo (b b' x : α) : ((b ⊓ x ≤ b') ∧ ¬(b' ⊓ x ≤ b)) ↔ (b ⊓ x < b' ⊓ x) := 
-- begin
--   split, 
--   { rintros ⟨h₁,h₂⟩, 
--     exact lt_of_le_of_ne (le_inf h₁ inf_le_right) (λ h_eq, h₂ (by {rw ←h_eq, exact inf_le_left}))},
--   exact λ h, ⟨(le_inf_iff.mp h.le).1,λ h', h.ne.symm ((le_inf h' inf_le_right).antisymm h.le)⟩, 
-- end 

-- lemma bar (p q a b x : α) (hpa : p < a) (hab : a < b) (hbq : b < q) (hpx : p < x) (hxq : x < q):
--   (p < x ⊓ b) ∨ (a ⊔ x < q) := 
-- begin
--   by_contradiction h, 
--   push_neg at h, 
--   have hp := le_inf hpx.le hpa.le ,  
--   have hq := sup_le hxq.le hbq.le ,  
--   have hp' : p ≤ x ⊓ b := le_inf hpx.le (hpa.le.trans hab.le), 
--   have hq' : a ⊔ x ≤ q := sup_le (hab.le.trans hbq.le) hxq.le , 
--   have hp'' := eq_of_le_of_not_lt hp' h.1, 
--   have hq'' := eq_of_le_of_not_lt hq' h.2, 
--   subst hp'', 
--   subst hq'',
--   refine hab.ne (@eq_of_le_of_inf_le_of_sup_le _ _ _ _ _ x hab.le _ _), 
--   { rwa [@inf_comm _ _ b, @inf_comm _ _ a]},
--   { rwa [@sup_comm _ _ b], },
-- end 

-- lemma spanning.foo (hb : M.basis b) (x : α) : 
-- --  ∃ b', b' ≤ x ⊔ b ∧ M.basis b' ∧ (M.basis_of (b' ⊓ x) x) :=
-- -- ∃ b'  b' ≤ x ⊔ b ∧ M.basis b' ∧ (M.basis b'' → b' ⊓ x ≤ b'' ⊓ x → b'' ⊓ x ≤ b' ⊓ x) :=
-- -- ∃ b', b' ≤ x ⊔ b ∧ M.basis b' ∧ (M.basis b'' → b' ⊓ x ≤ b'' ⊓ x → b'' ⊓ x ≤ b' ⊓ x) :=
-- -- ∃ b', b' ≤ x ⊔ b ∧ M.basis b' ∧ (M.basis b'' → b' ⊓ x ≤ b'' → b'' ⊓ x ≤ b') :=
-- -- <-> ∃ b', xᶜ ⊓ b ≤ b' ∧ M.basis b' ∧ (M.basis b'' → b'' ≤ b' ⊔ xᶜ → b' ≤ b'' ⊔ xᶜ) :=
-- ∃ b', b ≤ b' ⊔ x ∧ M.basis b' ∧ ∀ b'', M.basis b'' → ¬ (b'' ⊓ x < b' ⊓ x) :=
-- begin
--   obtain ⟨b',hb'x, hb', hb'1⟩ := hb.exists_extension_from x, 
--   refine ⟨b', _,hb', λ b'' hb'' hb''x , _⟩, 
  
--   obtain ⟨b₁,hb₁,hxb1⟩ := (hb'.inf_right_indep x).le_basis_sup hb, 
--   have := hb'1.eq_of_le_indep (le_inf hxb1.1 inf_le_right) inf_le_right (hb₁.inf_right_indep _),
-- end 

end supermatroid