
import .basic'

universes u v

section dual 

variables {α : Type u} [lattice α] [bounded_order α]

namespace supermatroid



lemma dual_max_sup (M : supermatroid α) : @max_inf αᵒᵈ _ M.basis :=
begin
  intros x b hb, 
  obtain ⟨b',hb'x,hb', hb'xx⟩:=  hb.exists_extension_from x, 
  refine ⟨b',hb',(sup_le (by rwa sup_comm) le_sup_right : b' ⊔ x ≤ b ⊔ x), 
    λ b'' hb'' hb''x, le_antisymm hb''x (le_inf (_ : b' ≤ b'' ⊔ x) inf_le_right)⟩, 
  obtain ⟨hb''b',-⟩  := (@sup_le_iff α _ _ _ _).mp hb''x, 
  clear hb''x, 
  
  -- I don't think this works. To be continued... 
  
  

  
  --have := M.basis_max_sup x b hb, 

end 

def lattice_dual (M : supermatroid α) : supermatroid (αᵒᵈ) :=  
{ basis := M.basis,
  basis_nonempty := M.basis_nonempty,
  basis_antichain := M.basis_antichain.to_dual,
  basis_middle := 
  begin
    rintros x y b hb b' hb' hxy hxb hb'y,
    obtain ⟨b₀,hb₀,hyb₀,hb₀x⟩ := M.basis_middle y x b' hb' b hb hxy hb'y hxb, 
    exact ⟨b₀, hb₀, hb₀x, hyb₀⟩, 
  end,
  basis_max_inf := sorry,
  basis_max_sup := sorry }

end dual 
