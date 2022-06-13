
import .basic 

universes u v

variables {α : Type u} [lattice α] [is_modular_lattice α] [bounded_order α] 
  {M : supermatroid α} {i j b x y c d r : α}

namespace supermatroid

lemma spanning.foo (hb : M.basis b) (x : α) : 
--  ∃ b', b' ≤ x ⊔ b ∧ M.basis b' ∧ (M.basis_of (b' ⊓ x) x) :=
-- ∃ b'  b' ≤ x ⊔ b ∧ M.basis b' ∧ (M.basis b'' → b' ⊓ x ≤ b'' ⊓ x → b'' ⊓ x ≤ b' ⊓ x) :=
-- ∃ b', b' ≤ x ⊔ b ∧ M.basis b' ∧ (M.basis b'' → b' ⊓ x ≤ b'' ⊓ x → b'' ⊓ x ≤ b' ⊓ x) :=
-- ∃ b', b' ≤ x ⊔ b ∧ M.basis b' ∧ (M.basis b'' → b' ⊓ x ≤ b'' → b'' ⊓ x ≤ b') :=
-- <-> ∃ b', xᶜ ⊓ b ≤ b' ∧ M.basis b' ∧ (M.basis b'' → b'' ≤ b' ⊔ xᶜ → b' ≤ b'' ⊔ xᶜ) :=
∃ b', b ≤ b' ⊔ x ∧ M.basis b' ∧ ∀ b'', M.basis b'' → b'' ⊓ x ≤ b' → b' ⊓ x ≤ b'' :=
begin
  obtain ⟨b',hb'x, hb', hb'1⟩ := hb.exists_extension_from x, 
  refine ⟨b', _,hb', λ b'' hb'' hb''x , _⟩, 
  
  obtain ⟨b₁,hb₁,hxb1⟩ := (hb'.inf_right_indep x).le_basis_sup hb, 
  have := hb'1.eq_of_le_indep (le_inf hxb1.1 inf_le_right) inf_le_right (hb₁.inf_right_indep _),
end 

end supermatroid