import Mathlib.SetTheory.Ordinal.Basic

import Mathlib.Init.Algebra.Order
import Mathlib.CategoryTheory.Category.Preorder



-- Unbundled version of the 'WellOrder' type
class WellOrderUnbundled (α : Type v) extends LinearOrder α :=
  wo : IsWellOrder α (· < ·)




namespace WellOrderUnbundled


#check WellFounded.induction

theorem inf_exists
  {α : Type v} [iwo : WellOrderUnbundled α]
  (p : α → Prop)
  (h : ∃ β, p β)
  : ∃ μ, p μ ∧ ∀ β, p β → μ ≤ β := by
  have he : α → Prop :=
    fun β => ∃ γ ≤ β, p γ
  have hc : Prop :=
    ∃ μ, p μ ∧ ∀ γ, p γ → μ ≤ γ
  have rs : ∀ β, (∀ γ, (γ < β → he γ → hc)) → (he β → hc) := by
    intro β hr t
    sorry
  rcases h with ⟨β, hβ⟩
  have test := WellFounded.induction iwo.wo.wf β rs
  have q : he β := by
    sorry -- Il suffit de pouvoir lire à travers rh..., car p β
  have i : hc := test q
  -- hc est EXACTEMENT notre conclusion...
  sorry


-- Take the element whose existence is guaranteed by inf_exists
noncomputable def inf
  {α : Type v} [WellOrderUnbundled α]
  (p : α → Prop)
  (h : ∃ β, p β)
  : α :=
  sorry

lemma inf_is_in
  {α : Type v} [WellOrderUnbundled α]
  (p : α → Prop)
  (h : ∃ β, p β) :
  p (inf p h) := by
  sorry

lemma inf_is_le
  {α : Type v} [WellOrderUnbundled α]
  (p : α → Prop)
  (h : ∃ β, p β) :
  ∀ β, p β → (inf p h) ≤ β := by
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
  exact t


end WellOrderUnbundled

-- End of 'namespace WellOrderUnbundled'

open WellOrderUnbundled


variable {α : Type v} [hwos : WellOrderUnbundled α] [NoMaxOrder α]

noncomputable
instance SuccOrder.ofWellOrder : SuccOrder α where
  succ β := succMap β (not_isMax β) 
  le_succ := by
    intro β
    dsimp only
    have t : β < succMap β (not_isMax β) :=
      succMap_lt β (not_isMax β)
    exact LT.lt.le t
  max_of_succ_le := by
    intro β
    simp only [not_isMax]
    have t : β < succMap β (not_isMax β) :=
      succMap_lt β (not_isMax β)
    intro h
    have s : β < β := lt_of_lt_of_le t h
    apply lt_irrefl β
    assumption
  succ_le_of_lt := by
    intro β γ
    simp only [not_isMax]
    intro h
    exact succMap_le_of_lt (not_isMax β) h
  le_of_lt_succ := by
    intro β γ h
    by_contra ha
    have h₁ : β < succMap β (not_isMax β) :=
      succMap_lt β (not_isMax β)
    have h₂ :=
      le_trans
        (succMap_le_of_lt (not_isMax β) h)
        (succMap_le_of_lt (not_isMax γ) (lt_of_not_le ha))
    exact LT.lt.false (lt_of_lt_of_le h₁ h₂)
    

-- #check WellOrder

variable  (α : Type v) [h : WellOrderUnbundled α]
#check WellOrder.mk α (· < · ) h.wo

noncomputable instance
  (α : Type v) [WellOrderUnbundled α] [ne : Nonempty α]
  : Zero α where
  zero := inf (fun _ => True) (by use ne.some)

noncomputable instance
  (α : Type v) [WellOrderUnbundled α] [Nonempty α]
  : OrderBot α where
  bot := 0
  bot_le := by
    intro β
    dsimp only
    have h := inf_is_le (fun _ => True) (by use β) β
    apply h
    exact trivial

-- unused?
def WellOrderUnbundled.initial (α : Type v) [WellOrderUnbundled α] (β : α) :=
  {γ : α // γ < β}

-- We still have a well founded order by restricting it
instance WellOrderUnbundled.ofInitial (α : Type v) [WellOrderUnbundled α] (β : α)
  : WellOrderUnbundled (WellOrderUnbundled.initial α β) :=
  sorry