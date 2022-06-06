import tactic 
import order.antichain 
import order.minimal
import order.upper_lower 
import order.lattice_intervals

universes u_1 u_2

noncomputable theory 

variables {α : Type u_1} {β : Type u_2}  {s t : set α}

-- lemma disjoint.mem_inter_elim {γ : Sort*} {x : α} (hst : disjoint s t) (hx : x ∈ s ∩ t) : γ := 
-- (set.not_mem_empty _ ((set.disjoint_iff_inter_eq_empty.mp hst).subst hx)).elim 

lemma disjoint_iff_le_compl_right [boolean_algebra α] {s t : α}: disjoint s t ↔ s ≤ tᶜ := 
by {rw is_compl.disjoint_left_iff is_compl_compl}

lemma disjoint_iff_le_compl_left [boolean_algebra α] {s t : α}: disjoint s t ↔ t ≤ sᶜ := 
by rw [disjoint.comm, disjoint_iff_le_compl_right]

lemma mem_compl_image' [boolean_algebra α] {a : α} {s : set α}: a ∈ compl '' s ↔ aᶜ ∈ s := 
begin
  rw [set.mem_image], 
  exact ⟨λ h, exists.elim h (λ x hx, by {rw [←hx.2, compl_compl], exact hx.1}), 
    λ h, ⟨_,h,compl_compl _⟩⟩, 
end 

@[simp] lemma compl_compl_image' [boolean_algebra α] {s : set α} : compl '' (compl '' s) = s := 
by {ext, simp}

lemma is_antichain.img_iso [has_le α] [has_le β] (hs : is_antichain (≤) s) (φ : order_iso α β) :
  is_antichain (≤) (φ '' s) :=
begin
  intros b hb b' hb' h₁ h₂, 
  rw set.mem_image at hb hb', 
  obtain ⟨⟨a,has,rfl⟩,⟨a',has',rfl⟩⟩ := ⟨hb,hb'⟩, 
  exact hs has has' (λ haa', h₁ (haa'.subst (by refl))) (φ.le_iff_le.mp h₂), 
end 

lemma is_antichain.img_compl [boolean_algebra α] (hs : is_antichain (≤) s):
  is_antichain (≤) (compl '' s) :=
(hs.img_iso (order_iso.compl α)).flip

lemma is_antichain.max_lower_set_of [partial_order α] (hs : is_antichain (≤) s) :
  maximals (≤) {x | ∃ y ∈ s, x ≤ y} = s :=
begin
  ext x, 
  simp only [maximals, exists_prop, set.mem_set_of_eq, forall_exists_index, and_imp, set.sep_set_of],
  refine ⟨λ h, exists.elim h.1 (λ y hy, ((h.2 _ hy.1 rfl.le hy.2).symm.subst hy.1)), 
    λ h, ⟨⟨x,h,rfl.le⟩,λ b y hy hby hxy, _⟩⟩,  
  have : x = y := by_contra (λ h_eq, (hs h hy h_eq (hxy.trans hby)).elim), 
  exact hxy.antisymm (this.symm.subst hby), 
end 

lemma is_antichain.min_upper_set_of [partial_order α] (hS : is_antichain (≤) s) :
  minimals (≤) {x | ∃ y ∈ s, y ≤ x} = s :=
begin
  ext x, 
  simp only [minimals, exists_prop, set.mem_set_of_eq, forall_exists_index, and_imp, set.sep_set_of], 
  refine ⟨λ h, exists.elim h.1 (λ y hy, ((h.2 _ hy.1 rfl.le hy.2).symm.subst hy.1)), 
    λ h, ⟨⟨x,h,rfl.le⟩,λ b y hy hby hxy, _⟩⟩,  
  have : y = x := by_contra (λ h_eq, hS hy h h_eq (hby.trans hxy)), 
  exact (this.subst hby).antisymm hxy, 
end



