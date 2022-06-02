
import order.lattice_intervals

universe u 
open set 

variables {α : Type u}

namespace Icc 

instance distrib_lattice [distrib_lattice α] {a b : α} : distrib_lattice (Icc a b) := 
{ le_sup_inf := λ x y z, subtype.mk_le_mk.mpr (distrib_lattice.le_sup_inf x y z) , .. Icc.lattice }

@[reducible] def boolean_algebra [boolean_algebra α] {a b : α} (hab : a ≤ b) :
  boolean_algebra (Icc a b) := 
{ compl := λ x, ⟨a ⊔ (xᶜ ⊓ b), ⟨le_sup_left, sup_le hab inf_le_right⟩⟩,
  sdiff := λ x y, x ⊓ ⟨a ⊔ (yᶜ ⊓ b), ⟨le_sup_left, sup_le hab inf_le_right⟩⟩,
  sdiff_eq := λ x y, rfl,  
  bot := ⟨a, ⟨rfl.le, hab⟩⟩,
  sup_inf_sdiff := 
  begin
    rintros ⟨x,hx⟩ ⟨y,hy⟩, 
    suffices h : x ⊓ y ⊔ (x ⊓ (a ⊔ (yᶜ ⊓ b))) = x, from subtype.mk_eq_mk.mpr h,
    rw [←inf_sup_left, sup_inf_left, @sup_comm α _ a, sup_inf_left, ←sup_assoc, ←sup_assoc], 
    simp only [sup_compl_eq_top, top_sup_eq, top_inf_eq, inf_eq_left], 
    exact hx.2.trans le_sup_right, 
  end,
  inf_inf_sdiff := 
  begin
    rintros ⟨x,hx⟩ ⟨y,hy⟩, 
    suffices h : (x : α) ⊓ y ⊓ (x ⊓ (a ⊔ (yᶜ ⊓ b))) = a, from subtype.mk_eq_mk.mpr h, 
    rw [inf_right_comm, ←inf_assoc, inf_idem],
    refine le_antisymm _ (le_inf (le_inf hx.1 (le_sup_left)) hy.1), 
    rw [inf_assoc, inf_sup_right, inf_right_comm, compl_inf_eq_bot, bot_inf_eq, sup_bot_eq, 
      inf_left_comm], 
    exact inf_le_left, 
  end,
  top := ⟨b, ⟨hab, rfl.le⟩⟩,
  inf_compl_le_bot := 
  begin
    intro x,
    suffices h : (x : α) ⊓ (a ⊔ (xᶜ ⊓ b)) ≤ a, from subtype.mk_le_mk.mpr h,
    simp [inf_sup_left, ←inf_assoc], 
  end,
  top_le_sup_compl := 
  begin
    intro x,
    suffices h : b ≤ x ⊔ (a ⊔ (xᶜ ⊓ b)), from subtype.mk_le_mk.mpr h, 
    simp only [sup_compl_eq_top, @sup_comm _ _ a, sup_inf_left, top_sup_eq, top_inf_eq, ←sup_assoc, 
    sup_right_comm],
    exact le_sup_right, 
  end,
  le_top := λ a, a.2.2,
  bot_le := λ a, a.2.1, 
  le_sup_inf := λ x y z, subtype.mk_le_mk.mpr (boolean_algebra.le_sup_inf x y z),
  ..Icc.lattice, 
  ..Icc.bounded_order hab, }

end Icc 

namespace Ici

instance distrib_lattice [distrib_lattice α] {a : α} : distrib_lattice (Ici a) :=
{ le_sup_inf := λ x y z, subtype.mk_le_mk.mpr (distrib_lattice.le_sup_inf x y z), .. Ici.lattice }

instance boolean_algebra [boolean_algebra α] {a : α} : boolean_algebra (Ici a) := 
{ compl := λ x, ⟨a ⊔ xᶜ, (le_sup_left : a ≤ a ⊔ xᶜ)⟩,
  sdiff := λ x y, x ⊓ ⟨a ⊔ yᶜ, (le_sup_left : a ≤ a ⊔ yᶜ)⟩,
  sdiff_eq := λ x y, sorry,  
  bot := ⟨a, rfl.le⟩,
  top := ⟨⊤, le_top⟩,
  sup_inf_sdiff := sorry,
  -- begin
  --   rintros ⟨x,hx⟩ ⟨y,hy⟩, 

  --   --suffices h : x ⊓ y ⊔ (x ⊓ (a ⊔ (yᶜ ⊓ b))) = x, from subtype.mk_eq_mk.mpr h,
  --   sorry
  -- end,
  inf_inf_sdiff := sorry,
  -- begin
  --   rintros ⟨x,hx⟩ ⟨y,hy⟩, 
  --   --suffices h : (x : α) ⊓ y ⊓ (x ⊓ (a ⊔ (yᶜ ⊓ b))) = a, from subtype.mk_eq_mk.mpr h, 
  --   sorry
  --end,
  
  inf_compl_le_bot := sorry,
  -- begin
  --   intro x,
  --   --suffices h : (x : α) ⊓ (a ⊔ (xᶜ ⊓ b)) ≤ a, from subtype.mk_le_mk.mpr h,
  --   sorry
  -- end,
  top_le_sup_compl := sorry, 
  -- begin
  --   intro x,
  --   sorry 
  -- end,
  le_top := sorry, 
  --by {rintros ⟨x,hx⟩, exact subtype.mk_le_mk.mpr (boolean_algebra.le_top x)},
  bot_le := sorry, 
  -- by {rintros ⟨x,hx⟩, exact subtype.mk_le_mk.mpr hx},
  le_sup_inf := λ x y z, sorry, 
  ..Icc.lattice, 
  ..Ici.bounded_order, }


end Ici 

namespace Iic

instance distrib_lattice [distrib_lattice α] {a : α} : distrib_lattice (Iic a) :=
{ le_sup_inf := λ x y z, subtype.mk_le_mk.mpr (distrib_lattice.le_sup_inf x y z), .. Iic.lattice }

end Iic