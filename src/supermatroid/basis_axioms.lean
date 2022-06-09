
import .basic 

universes u 

open set

variables {α : Type u} [lattice α] [bounded_order α] {x x' y y' a b b' b₀ c : α} 
  {M : supermatroid α}

def satisfies_middle_axiom (B : set α) : Prop := 
  ∀ x x' b b', x ≤ x' → x ≤ b → b' ≤ x' → b ∈ B → b' ∈ B → ∃ b₀ ∈ B, x ≤ b₀ ∧ b₀ ≤ x'

-- infinite axiom 
def satisfies_extension (B : set α) : Prop := 
  ∀ x b y, b ∈ B → x ≤ b → x ≤ y → (maximals (≤) ((Icc x y) ∩ {i | ∃ b' ∈ B, i ≤ b'})).nonempty 

def supermatroid_of_bases {B : set α} 
  (h_nonempty : nonempty B)
  (h_antichain : is_antichain (≤) B) 
  (h_mid : satisfies_middle_axiom B) 
  (h_ext : satisfies_extension B):
  supermatroid α := 
{ indep         := λ x, ∃ b ∈ B, x ≤ b,
  ind_nonempty  := h_nonempty.elim (λ b, ⟨(⊥ : α), ⟨b.1, b.2,bot_le⟩ ⟩),
  ind_lower_set := λ i j hji, by {rintro ⟨b,⟨hb,hib⟩⟩, exact ⟨b,⟨hb,hji.trans hib⟩⟩},
  ind_maximize := by {rintros i ⟨b,⟨hb,hib⟩⟩ b' hib', exact h_ext i b b' hb hib hib'},
  ind_augment   := 
  begin
    rintros i ⟨b,⟨hb,hib⟩⟩ b' hi hb', 
    erw h_antichain.max_lower_set_of at hi hb', 
    obtain ⟨b₀, ⟨hb₀, hib₀, hb₀b⟩⟩ :=  
      h_mid i (i ⊔ b') b b' le_sup_left hib le_sup_right hb hb', 
    exact ⟨b₀,⟨lt_of_le_of_ne hib₀ (λ h, hi (h.symm ▸ hb₀)),hb₀b⟩,b₀,hb₀,rfl.le⟩, 
  end}


lemma bases_satisfy_middle (M : supermatroid α) : satisfies_middle_axiom M.basis :=
begin
  intros x x' b b' hxx' hxb hb'x' hb hb', 
  obtain ⟨b₀,⟨hb₀,hxb₀,hb₀x⟩⟩ := (hb.indep_of_le hxb).le_basis_sup hb', 
  exact ⟨b₀, hb₀, hxb₀, hb₀x.trans (sup_le hxx' hb'x')⟩,
end 


lemma bases_satisfy_extension (M : supermatroid α) : satisfies_extension M.basis :=
begin
  intros x b y hb hxb hxy, 
  obtain ⟨j, hxj, hjy⟩ := (hb.indep_of_le hxb).le_basis_of hxy, 
  obtain ⟨b',⟨hjb',hb'⟩⟩ := hjy.indep.le_basis, 
  refine ⟨j,⟨⟨hxj,hjy.le⟩,⟨b',hb',hjb'⟩⟩, λ a hxa hay,_ ⟩, 
  obtain ⟨b'',hb'',hab''⟩ := hxa.2, 
  exact hjy.eq_of_le_indep hay hxa.1.2 (hb''.indep_of_le hab''), 
end 
