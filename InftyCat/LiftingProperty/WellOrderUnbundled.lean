import Mathlib.SetTheory.Ordinal.Basic

import Mathlib.Init.Algebra.Order
import Mathlib.CategoryTheory.Category.Preorder



-- Unbundled version of the 'WellOrder' type
class WellOrderUnbundled (α : Type v) extends LinearOrder α :=
  wo : IsWellOrder α (· < ·)



namespace WellOrderUnbundled

open SuccOrder


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

lemma inf_is_min
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
    rcases (inf_is_min p h) with ⟨q, _⟩
    exact q


lemma inf_is_le
  {α : Type v} [WellOrderUnbundled α]
  (p : α → Prop)
  (h : ∃ β, p β) :
  ∀ β, p β → (inf p h) ≤ β := by
    rcases (inf_is_min p h) with ⟨_, q⟩
    exact q

-- p (inf p h ) ∧ ∀ (β : α), p β → μ ≤ β


variable {α : Type v} [hwos : WellOrderUnbundled α]


lemma succ_cond (β : α) : ∃ γ, β < γ ∨ IsMax γ := by
  by_cases h : ∃ (γ : α), IsMax γ
  · rcases h with ⟨γ, hγ⟩
    use γ
    right
    assumption
  · push_neg at h
    have h := h β
    have hl : ∃ γ, β < γ := by
      by_contra ha
      push_neg at ha
      have _ : IsMax β := by
        intro γ _
        apply ha
      contradiction
    rcases hl with ⟨γ, hγ⟩
    use γ
    left
    assumption

noncomputable def succMap (β : α) : α :=
  inf (fun γ => β < γ ∨ IsMax γ) (succ_cond β)

/-
noncomputable def succMap (β : α) (h : ¬IsMax β) : α :=
  inf (β < ·) (Iff.mp not_isMax_iff h)
-/

lemma succMap_le (β : α) : β < succMap β ∨ IsMax β := by
  have p : β < (succMap β) ∨ IsMax (succMap β)  :=
    inf_is_in (fun γ => β < γ ∨ IsMax γ) (succ_cond β)
  by_cases h : IsMax β
  · right
    assumption
  · left
    by_cases ha : IsMax (succMap β)
    · by_contra hb
      push_neg at hb
      have heq : β = succMap β := le_antisymm (ha hb) hb
      rw [heq] at h
      contradiction
    · rcases p with (hl | hr)
      · assumption
      · contradiction
    

lemma succMap_le_of_lt {β γ : α} (h: β < γ) : succMap β ≤ γ := by
  have p : ∀ δ, ((β < δ  ∨ IsMax δ) → succMap β ≤ δ) :=
    inf_is_le (fun γ => β < γ ∨ IsMax γ) (succ_cond β)
  specialize p γ (by left; assumption)
  assumption



noncomputable instance [ne : Nonempty α] : Zero α where
  zero := inf (fun _ => True) (by use ne.some)

noncomputable instance [Nonempty α] : OrderBot α where
  bot := 0
  bot_le := by
    intro β
    dsimp only
    have h := inf_is_le (fun _ => True) (by use β) β
    apply h
    exact trivial




-- Add a SuccOrder structure on well orders

noncomputable instance [NoMaxOrder α] : SuccOrder α where
  succ β := succMap β
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


def is_limit [NoMaxOrder α] (β : α) : Prop := 
  (∃ γ, γ < β) ∧ (∀ γ, β ≠ succ γ)


theorem induction [Nonempty α] [NoMaxOrder α]
  {C : α → Prop}
  (B : C 0)
  (S : ∀ β, C β → C (succ β))
  (L : ∀ β, (is_limit β ∧ (∀ γ < β, C γ)) → C β)
  : ∀ β, C β := by
  by_contra ha
  push_neg at ha
  let μ := inf (fun β => ¬C β) ha
  have ⟨hμ, hmμ⟩ : ¬C μ ∧  ∀ β, ¬C β → μ ≤ β :=
    inf_is_min (fun β => ¬C β) ha
  by_cases hz : μ = 0
  · rw [←hz] at B
    contradiction
  · by_cases hlim : is_limit μ
    · have hn : ∀ γ < μ, C γ := by
        intro γ hγ
        by_contra hb
        have _ : μ ≤ γ := hmμ γ hb
        rw [lt_iff_le_not_le] at hγ
        have _ := hγ.2
        contradiction
      have _ : C μ := L μ ⟨hlim, hn⟩
      contradiction
    · have hs : ∃ γ, μ = succ γ := by
        by_contra hb
        push_neg at hb
        have hc : ∃ γ, γ < μ := by
          by_contra hd
          push_neg at hd
          have h₁ : μ ≤ 0 := hd 0
          have h₂ : 0 ≤ μ := by
            have hj : (0 : α) ≤ ⊥ := by
              simp only [le_bot_iff]
              trivial
            have hi : ⊥ ≤ μ := by simp only [bot_le]
            exact le_trans hj hi
          have _ := le_antisymm h₁ h₂
          contradiction
        have _ : is_limit μ := by
          constructor
          · exact hc
          · exact hb
        contradiction
      rcases hs with ⟨γ, hγ⟩
      have h₁ : γ < μ := by
        by_contra hb
        push_neg at hb
        have hc : succ γ ≤ γ := by
          rw [← hγ]
          exact hb
        have _ : IsMax γ := max_of_succ_le hc
        have _ : ¬IsMax γ := by
          simp only [gt_iff_lt, not_isMax, not_false_eq_true]
        contradiction
      have h₂ : C γ := by
        by_contra hb
        have _ : γ < γ := lt_of_lt_of_le h₁ (hmμ γ hb)
        apply lt_irrefl γ
        assumption
      have h₃ : C μ := by
        have hb : C (succ γ) := S γ h₂
        rw [←hγ] at hb
        assumption
      contradiction



/- This will enable us to construct mathematical objects by
   ordinal recursion -/

theorem fix_exists [Nonempty α] [NoMaxOrder α]
  {C : α → Sort*}
  (B : C 0)
  (S : (β : α) → C β → C (succ β))
  (L : (β : α) → is_limit β → ((γ : α) → γ < β → C γ) → C β)
  : ∃ F : (β : α) → C β,
    F 0 = B ∧
    (∀ γ, F (succ γ) = S γ (F γ)) ∧
    (∀ γ, ∀ (h : is_limit γ), F γ = L γ h (fun δ _ => F δ)) 
  := by
    sorry

