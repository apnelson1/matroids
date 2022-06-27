
import order.lattice_intervals
import order.rel_iso

universes u v 
open function set 

section intervals 

variables {α : Type u} {a b : α}

namespace Icc 

instance distrib_lattice [distrib_lattice α] : distrib_lattice (Icc a b) := 
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

instance distrib_lattice [distrib_lattice α] : distrib_lattice (Ici a) :=
{ le_sup_inf := λ x y z, subtype.mk_le_mk.mpr (distrib_lattice.le_sup_inf x y z), .. Ici.lattice }

instance boolean_algebra [boolean_algebra α] : boolean_algebra (Ici a) := 
{ compl := λ x, ⟨a ⊔ xᶜ, (le_sup_left : a ≤ a ⊔ xᶜ)⟩,
  sdiff := λ x y, x ⊓ ⟨a ⊔ yᶜ, (le_sup_left : a ≤ a ⊔ yᶜ)⟩,
  sdiff_eq := λ x y, rfl,  
  bot := ⟨a, rfl.le⟩,
  top := ⟨⊤, le_top⟩,
  sup_inf_sdiff := 
  begin
    rintros ⟨x,hx⟩ ⟨y,hy⟩, 
    suffices h : x ⊓ y ⊔ (x ⊓ (a ⊔ yᶜ)) = x, from subtype.mk_eq_mk.mpr h,
    simp [←inf_sup_left, sup_left_comm], 
  end,
  inf_inf_sdiff :=
  begin
    rintros ⟨x,hx⟩ ⟨y,hy⟩, 
    suffices h : x ⊓ y ⊓ (x ⊓ (a ⊔ yᶜ)) = a, from subtype.mk_eq_mk.mpr h, 
    rw [inf_right_comm, ←inf_assoc, inf_idem, inf_assoc, inf_sup_right, compl_inf_eq_bot, 
      sup_bot_eq, inf_eq_left.mpr hy, inf_eq_right.mpr hx], 
  end,
  inf_compl_le_bot := 
  begin
    rintro ⟨x,hx⟩,
    suffices h : (x : α) ⊓ (a ⊔ xᶜ) ≤ a, from subtype.mk_le_mk.mpr h, 
    simp [inf_sup_left],
  end,
  top_le_sup_compl := 
  begin
    rintro ⟨x,hx⟩,
    suffices h : ⊤ ≤ x ⊔ (a ⊔ xᶜ), from subtype.mk_le_mk.mpr h, 
    simp [sup_left_comm], 
  end,
  le_top := by {rintros ⟨x,hx⟩, exact subtype.mk_le_mk.mpr (boolean_algebra.le_top _)},
  bot_le := by {rintros ⟨x,hx⟩, exact subtype.mk_le_mk.mpr hx},
  le_sup_inf := by {rintros ⟨x,hx⟩ ⟨y,hy⟩ ⟨z,hz⟩, exact subtype.mk_le_mk.mpr 
    (boolean_algebra.le_sup_inf x y z),}, 
  ..Ici.lattice, 
  ..Ici.bounded_order, }
end Ici 

namespace Iic

instance distrib_lattice [distrib_lattice α] {a : α} : distrib_lattice (Iic a) :=
{ le_sup_inf := λ x y z, subtype.mk_le_mk.mpr (distrib_lattice.le_sup_inf x y z), .. Iic.lattice }

instance boolean_algebra [boolean_algebra α] {a : α} : boolean_algebra (Iic a) := 
{ compl := λ x, ⟨a ⊓ xᶜ, (inf_le_left)⟩,
  sdiff := λ x y, x ⊓ ⟨a ⊓ yᶜ, (inf_le_left)⟩,
  sdiff_eq := λ x y, rfl,  
  bot := ⟨⊥, bot_le⟩,
  top := ⟨a, rfl.le⟩,
  sup_inf_sdiff := 
  begin
    rintros ⟨x,hx⟩ ⟨y,hy⟩, 
    suffices h : x ⊓ y ⊔ (x ⊓ (a ⊓ yᶜ)) = x, from subtype.mk_eq_mk.mpr h,
    rw [←inf_sup_left, inf_eq_left, sup_inf_left, sup_compl_eq_top, inf_top_eq],
    exact le_trans hx (le_sup_right),    
  end,
  inf_inf_sdiff :=
  begin
    rintros ⟨x,hx⟩ ⟨y,hy⟩, 
    suffices h : x ⊓ y ⊓ (x ⊓ (a ⊓ yᶜ)) = ⊥, from subtype.mk_eq_mk.mpr h, 
    rw [inf_right_comm, ←inf_assoc, inf_idem, inf_assoc, inf_assoc, compl_inf_eq_bot, inf_bot_eq, 
    inf_bot_eq], 
  end,
  inf_compl_le_bot := 
  begin
    rintro ⟨x,hx⟩,
    suffices h : (x : α) ⊓ (a ⊓ xᶜ) ≤ ⊥, from subtype.mk_le_mk.mpr h, 
    simp [inf_left_comm], 
  end,
  top_le_sup_compl := 
  begin
    rintro ⟨x,hx⟩,
    suffices h : a ≤ x ⊔ (a ⊓ xᶜ), from subtype.mk_le_mk.mpr h, 
    simp [sup_inf_left], 
  end,
  le_top := by {rintros ⟨x,hx⟩, exact subtype.mk_le_mk.mpr hx},
  bot_le := by {rintros ⟨x,hx⟩, exact subtype.mk_le_mk.mpr (boolean_algebra.bot_le x), },
  le_sup_inf := by {rintros ⟨x,hx⟩ ⟨y,hy⟩ ⟨z,hz⟩, exact subtype.mk_le_mk.mpr 
    (boolean_algebra.le_sup_inf x y z),}, 
  ..Iic.lattice, 
  ..Iic.bounded_order, }

end Iic

section iso 

variables [boolean_algebra α]

lemma inf_compl_sup_compl_inf_sup_eq_self {x a b : α} (hax : a ≤ x) (hxb : x ≤ b) : 
  (x ⊓ a ᶜ ⊔ bᶜ) ⊓ b ⊔ a = x := 
by rw [inf_sup_right, compl_inf_eq_bot, sup_bot_eq, sup_inf_right, sup_inf_right, compl_sup_eq_top, 
  inf_top_eq, ←sup_inf_right, inf_eq_left.mpr hxb, sup_eq_left.mpr hax] 

/-- A canonical order isomorphism between `Icc a b` and `Icc bᶜ aᶜ` with respect to the primal 
  ordering `≤` in a boolean algebra as opposed to the dual  --/
@[simps apply]
def Icc_Icc_compl_iso (a b : α) :
  (Icc a b) ≃o (Icc bᶜ aᶜ)  := 
 
{ to_fun := λ x, ⟨x ⊓ aᶜ ⊔ bᶜ, 
  ⟨le_sup_right, sup_le_iff.mpr ⟨inf_le_right, compl_le_compl (x.2.1.trans x.2.2)⟩⟩⟩, 
  inv_fun := λ x, ⟨x ⊓ b ⊔ a, ⟨le_sup_right, 
    sup_le_iff.mpr ⟨inf_le_right, (compl_le_compl_iff_le.mp (x.2.1.trans x.2.2))⟩⟩⟩, 
  left_inv := by {rintro ⟨x,hx⟩, simp only [subtype.coe_mk, subtype.mk_eq_mk, 
    inf_compl_sup_compl_inf_sup_eq_self hx.1 hx.2]},
  right_inv := by {rintro ⟨x,hx⟩, simp only [subtype.coe_mk, subtype.mk_eq_mk], 
    convert inf_compl_sup_compl_inf_sup_eq_self hx.1 hx.2; simp},
  map_rel_iff' := 
  begin 
    rintros ⟨x,⟨hax,hxb⟩⟩ ⟨y,⟨hay,hyb⟩⟩, 
    simp only [le_sup_right, sup_le_iff, subtype.coe_mk, equiv.coe_fn_mk, subtype.mk_le_mk, 
      and_true],
    rw [sup_inf_right, ←compl_inf, inf_eq_left.mpr (hax.trans hxb)], 
    refine ⟨λ h, _, λ h, inf_le_inf_right _ (le_sup_of_le_left h)⟩, 
    rw [←sup_inf_sdiff x a, inf_eq_right.mpr hax, sdiff_eq], 
    refine sup_le hay ((le_inf (inf_le_of_left_le hxb) h).trans _),
    rw [inf_left_comm, ←inf_assoc, inf_sup_right, compl_inf_eq_bot, sup_bot_eq, inf_assoc],
    exact inf_le_left,
  end  }

@[simps apply]  
def Icc_Icc_compl_iso' (a b : α) :
  (Icc a bᶜ) ≃o (Icc b aᶜ)  := 
(Icc_Icc_compl_iso a bᶜ).trans (order_iso.set_congr (Icc bᶜᶜ aᶜ) (Icc b aᶜ) (by rw compl_compl))

--@[simps apply]
def Iic_Ici_compl_iso (a : α): 
  Iic a ≃o Ici aᶜ :=
(order_iso.set_congr (Iic a) (Icc ⊥ a) Icc_bot.symm).trans 
  ((Icc_Icc_compl_iso ⊥ a).trans 
    (order_iso.set_congr (Icc aᶜ ⊥ᶜ) (Ici aᶜ) (by rw [compl_bot, Icc_top])))


-- @[simp] lemma Iic_Ici_compl_iso_apply (a : α) (x : ↥(Iic a)) : 
--   (Iic_Ici_compl_iso a) x = ⟨x ⊔ aᶜ, by {sorry }⟩ :=
-- begin
--   by simp [Iic_Ici_compl_iso], 
-- end 



end iso 

end intervals 


-- section iso_image 

-- variables {α : Type u} {β : Type v} [has_le β]

-- def order_iso.image_semilattice_sup [semilattice_sup α] (φ : α ≃o β) : semilattice_sup β :=
-- { sup := λ x y, φ (φ.symm x ⊔ φ.symm y),
--   le := λ x y, φ.symm x ≤ φ.symm y,
--   lt := λ x y, φ.symm x < φ.symm y,
--   le_refl := λ x, rfl.le,
--   le_trans := λ _ _ _, le_trans,
--   lt_iff_le_not_le := λ x y, lt_iff_le_not_le,
--   le_antisymm := λ x y hxy hyx, φ.symm.injective (le_antisymm hxy hyx),
--   le_sup_left := λ x y, (order_iso.symm_apply_apply φ _).symm.subst le_sup_left, 
--   le_sup_right := λ x y, (order_iso.symm_apply_apply φ _).symm.subst le_sup_right, 
--   sup_le := λ x y z hxy hyz, by {rw ←order_iso.map_sup,   }  }

-- def order_iso.boolean_algebra {α : Type u} {β : Type v} [boolean_algebra α] [has_le β] (φ : α ≃o β) :
--   boolean_algebra β := { 
  
  
--   sup_le := λ x y z, by {
--     sorry,
--   },
--   inf := sorry,
--   inf_le_left := sorry,
--   inf_le_right := sorry,
--   le_inf := sorry,
--   le_sup_inf := sorry,
--   sdiff := sorry,
--   bot := sorry,
--   sup_inf_sdiff := sorry,
--   inf_inf_sdiff := sorry,
--   compl := sorry,
--   top := sorry,
--   inf_compl_le_bot := sorry,
--   top_le_sup_compl := sorry,
--   le_top := sorry,
--   bot_le := sorry,
--   sdiff_eq := sorry }
-- --instance boolean_algebra [boolean_algebra α] {a : α} : boolean_algebra (Ici a) 


-- end iso_image