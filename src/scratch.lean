import data.fin.basic

example {α : Type} [preorder α] {P : α → Prop} {n : ℕ} {f : fin n.succ → α} (hf : monotone f) 
(hP : ∀ (a b : α), a ≤ b → P a → P b) (h0 : P (f 0)) : P (f (fin.last n)) := 
by {}
