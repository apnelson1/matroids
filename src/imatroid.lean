import tactic 

universes u v

variables {E : Type u}

def is_maximal_wrt (P : set E → Prop)(X : set E): Prop := 
  P X ∧ ∀ Y, X ⊂ Y → ¬ P Y 

structure imatroid (E : Type u):= 
  (indep : set E → Prop)
  (empty_indep : indep ∅) 
  (indep_monotone : ∀ I J, indep J → I ⊆ J → indep I)
  (indep_augment : 
    ∀ I J, ¬ is_maximal_wrt indep I → is_maximal_wrt indep J → 
      ∃ x, x ∈ J \ I ∧ indep (I.insert x))
  (indep_extension :
    ∀ I X, indep I → I ⊆ X → 
      ∃ J, is_maximal_wrt (λ (Y : set E), I ⊆ Y ∧ Y ⊆ X ∧ indep Y) J)

  
