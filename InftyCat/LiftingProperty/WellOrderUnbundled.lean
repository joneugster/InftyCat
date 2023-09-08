import Mathlib.SetTheory.Ordinal.Basic

import Mathlib.Init.Algebra.Order
import Mathlib.CategoryTheory.Category.Preorder



-- Unbundled version of the 'WellOrder' type
class WellOrderUnbundled (α : Type v) extends LinearOrder α :=
  wo : IsWellOrder α (· < ·)



namespace WellOrderUnbundled


theorem inf_exists
  {α : Type v} [iwo : WellOrderUnbundled α]
  (p : α → Prop)
  (h : ∃ β, p β)
  : ∃ μ, p μ ∧ ∀ β, p β → μ ≤ β := by
  let hc : Prop :=
    ∃ μ, p μ ∧ ∀ β, p β → μ ≤ β
  have rs
  : ∀ β, (∀ γ, (γ < β → (∃ μ ≤ γ, p μ) → hc)) → ((∃ μ ≤ β, p μ) → hc) := by
    intro β hr t
    show ∃ μ, p μ ∧ ∀ β, p β → μ ≤ β
    by_cases hmax : ∀ μ < β, ¬p μ
    · use β
      constructor
      · rcases t with ⟨μ, ⟨hμ, hpμ⟩⟩
        have heq : β = μ := by
          by_contra habs
          specialize hmax μ
          have _ := hmax (Ne.lt_of_le' habs hμ)
          contradiction
        rw [heq]
        trivial
      · intro γ hγ
        by_contra habs
        rw [@not_le] at habs
        specialize hmax γ
        have _ := hmax habs
        contradiction
    · push_neg at hmax
      rcases hmax with ⟨γ, ⟨hγ, hpγ⟩⟩
      have hs : ∃ μ ≤ γ, p μ := by use γ
      specialize hr γ hγ hs
      trivial
  rcases h with ⟨β, hβ⟩
  have test := WellFounded.induction iwo.wo.wf β rs
  have q : ∃ μ ≤ β, p μ := by use β
  show hc
  exact test q




-- Take the element whose existence is guaranteed by inf_exists
noncomputable def inf
  {α : Type v} [WellOrderUnbundled α]
  (p : α → Prop)
  (h : ∃ β, p β)
  : α :=
  have hq : ∃ (_ : {μ // p μ ∧ ∀ β, p β → μ ≤ β}), True := by
    rcases (inf_exists p h) with ⟨β, hβ⟩
    use ⟨β, hβ⟩
  (Classical.choice (nonempty_of_exists hq)).val

lemma inf_is_inf
  {α : Type v} [WellOrderUnbundled α]
  (p : α → Prop)
  (h : ∃ β, p β) :
  p (inf p h) ∧ ∀ β, p β → (inf p h) ≤ β := by
    unfold inf
    have hq : ∃ (_ : {μ // p μ ∧ ∀ β, p β → μ ≤ β}), True := by
      rcases (inf_exists p h) with ⟨β, hβ⟩
      use ⟨β, hβ⟩
    exact (Classical.choice (nonempty_of_exists hq)).property

lemma inf_is_in
  {α : Type v} [WellOrderUnbundled α]
  (p : α → Prop)
  (h : ∃ β, p β) :
  p (inf p h) := by
    rcases (inf_is_inf p h) with ⟨q, _⟩
    exact q


lemma inf_is_le
  {α : Type v} [WellOrderUnbundled α]
  (p : α → Prop)
  (h : ∃ β, p β) :
  ∀ β, p β → (inf p h) ≤ β := by
    rcases (inf_is_inf p h) with ⟨_, q⟩
    exact q

-- p (inf p h ) ∧ ∀ (β : α), p β → μ ≤ β


variable {α : Type v} [WellOrderUnbundled α]

noncomputable def succMap (β : α) (h : ¬IsMax β) : α :=
  inf (β < ·) (Iff.mp not_isMax_iff h)

lemma succMap_lt (β : α) (h : ¬IsMax β) : β < succMap β h :=
  inf_is_in (β < ·) (Iff.mp not_isMax_iff h)

lemma succMap_le_of_lt {β γ : α} (h : ¬IsMax β) (hc: β < γ)
  : succMap β h ≤ γ := by
  have t := inf_is_le (β < ·) (Iff.mp not_isMax_iff h)
  specialize t γ hc
  exact t



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

