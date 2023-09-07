import Mathlib.SetTheory.Ordinal.Basic

import Mathlib.Init.Algebra.Order
import Mathlib.CategoryTheory.Category.Preorder



-- Unbundled version of the 'WellOrder' type
class WellOrderUnbundled (α : Type v) extends LinearOrder α :=
  wo : IsWellOrder α (· < ·)



namespace WellOrderUnbundled

noncomputable def inf
  {α : Type v} [WellOrderUnbundled α]
  (p : α → Prop)
  (h : ∃ (β : α), p β)
  : α :=
  sorry

lemma inf_is_in
  {α : Type v} [WellOrderUnbundled α]
  (p : α → Prop)
  (h : ∃ (β : α), p β) :
  p (inf p h) := by
  sorry

lemma inf_is_le
  {α : Type v} [WellOrderUnbundled α]
  (p : α → Prop)
  (h : ∃ (β : α), p β) :
  ∀ (β : α), p β → (inf p h) ≤ β := by
  sorry

-- p (inf p h ) ∧ ∀ (β : α), p β → μ ≤ β


variable {α : Type v} [WellOrderUnbundled α]

noncomputable def succMap (β : α) (h : ¬IsMax β) : α :=
  inf (β < ·) (Iff.mp not_isMax_iff h)

lemma succMap_lt (β : α) (h : ¬IsMax β) : β < succMap β h :=
  inf_is_in (β < ·) (Iff.mp not_isMax_iff h)

lemma succMap_le_of_lt {β γ : α} (h : ¬IsMax β) (hc: β < γ)
  : succMap β h ≤ γ := by
  have t := inf_is_le (β < ·) (Iff.mp not_isMax_iff h)
  specialize t γ
  specialize t hc
  
  sorry



end WellOrderUnbundled

-- End of 'namespace WellOrderUnbundled'

open WellOrderUnbundled


variable {α : Type v} [hwos : WellOrderUnbundled α] [NoMaxOrder α]

noncomputable
instance SuccOrder.ofWellOrder : SuccOrder α where
  succ β := WellOrderUnbundled.succMap β (not_isMax β) 
  le_succ := by
    intro β
    dsimp only
    have t : β < WellOrderUnbundled.succMap β (not_isMax β) :=
      WellOrderUnbundled.succMap_lt β (not_isMax β)
    exact LT.lt.le t
  max_of_succ_le := by
    intro β
    simp only [not_isMax]
    have t : β < WellOrderUnbundled.succMap β (not_isMax β) :=
      WellOrderUnbundled.succMap_lt β (not_isMax β)
    intro h
    have s : β < β := lt_of_lt_of_le t h
    apply lt_irrefl β
    assumption
  succ_le_of_lt := by
    intro β γ
    simp only [not_isMax]

  le_of_lt_succ := sorry

-- #check WellOrder
-- def WellOrderUnbundled.bundle (α : Type v) [h : WellOrderUnbundled α]
--   : WellOrder.{v} where
--   α := α
--   r := (· < · )
--   wo := h.wo

-- -- structure WellOrder : Type (u + 1) where
-- --   /-- The underlying type of the order. -/
-- --   α : Type u
-- --   /-- The underlying relation of the order. -/
-- --   r : α → α → Prop
-- --   /-- The proposition that `r` is a well-ordering for `α`. -/
-- --   wo : IsWellOrder α r

variable  (α : Type v) [h : WellOrderUnbundled α]
#check WellOrder.mk α (· < · ) h.wo

instance (α : Type v) [WellOrderUnbundled α] : Zero α where
  zero := _

instance (α : Type v) [WellOrderUnbundled α] : Bot α where
  bot := 0

-- unused?
def WellOrderUnbundled.initial (α : Type v) [WellOrderUnbundled α] (β : α) :=
  {γ : α // γ < β}

-- We still have a well founded order by restricting it
instance WellOrderUnbundled.ofInitial (α : Type v) [WellOrderUnbundled α] (β : α)
  : WellOrderUnbundled (WellOrderUnbundled.initial α β) :=
  sorry