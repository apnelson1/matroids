import tactic

universe u

variables {α : Type u} [lattice α] 

lemma inf_le_inf_of_inf_le {a b x : α} (h : a ⊓ x ≤ b) : a ⊓ x ≤ b ⊓ x := by simp [h]

lemma sup_le_sup_of_le_sup {a b x : α} (h : a ≤ b ⊔ x) : a ⊔ x ≤ b ⊔ x := by simp [h]

lemma inf_eq_inf_of_le_of_le {a b x : α} (h1 : a ⊓ x ≤ b) (h2 : b ⊓ x ≤ a) : a ⊓ x = b ⊓ x :=
  le_antisymm (inf_le_inf_of_inf_le h1) (inf_le_inf_of_inf_le h2)

lemma sup_eq_sup_of_le_of_le {a b x : α} (h1 : a ≤ b ⊔ x) (h2 : b ≤ a ⊔ x) : a ⊔ x = b ⊔ x := 
  le_antisymm (sup_le_sup_of_le_sup h1) (sup_le_sup_of_le_sup h2)
