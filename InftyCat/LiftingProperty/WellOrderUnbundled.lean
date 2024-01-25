import Mathlib.SetTheory.Ordinal.Basic

import Mathlib.Init.Algebra.Order
import Mathlib.CategoryTheory.Category.Preorder



-- Unbundled version of the 'WellOrder' type
class WellOrderUnbundled (α : Type v) extends LinearOrder α :=
  iwf : IsWellFounded α (· < ·)



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
  have test := WellFounded.induction iwo.iwf.wf β rs
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

lemma succMap_le (β : α) : β < succMap β ∨ (IsMax β ∧ β = (succMap β)) := by
  have p : β < (succMap β) ∨ IsMax (succMap β)  :=
    inf_is_in (fun γ => β < γ ∨ IsMax γ) (succ_cond β)
  by_cases h : IsMax β
  · right
    constructor
    · assumption
    · cases p with
    | inl hp =>
      have _ : ¬(β < succMap β) := IsMax.not_lt h
      contradiction
    | inr hp =>
      exact le_antisymm
        (le_of_not_lt (IsMax.not_lt hp))
        (le_of_not_lt (IsMax.not_lt h))
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

noncomputable instance : WellOrderUnbundled (WithTop α) where
  iwf := {
    wf := WithTop.wellFounded_lt hwos.iwf.wf
  }




-- Add a SuccOrder structure on well orders

noncomputable instance : SuccOrder α where
  succ := succMap
  le_succ := by
    intro β
    cases (succMap_le β) with
    | inl h =>
      exact LT.lt.le h
    | inr h =>
      exact Eq.le h.right
  max_of_succ_le := by
    intro β
    intro hi
    cases (succMap_le β) with
    | inl h =>
      have _ : β < β := lt_of_lt_of_le h hi
      have _ := lt_irrefl β
      contradiction
    | inr h =>
      exact h.left
  succ_le_of_lt := by
    intro β γ
    intro hi
    exact succMap_le_of_lt hi
  le_of_lt_succ := by
    intro β γ h
    by_contra ha
    have hb : γ < β :=
      lt_of_not_ge ha
    have hc : succMap γ ≤ β :=
      succMap_le_of_lt hb
    cases (succMap_le γ) with
    | inl hp =>
      have _ : β < β := lt_of_lt_of_le h hc
      have _ := lt_irrefl β
      contradiction
    | inr hp =>
      have hy : ¬(γ < β) :=
        IsMax.not_lt hp.left 
      contradiction


def is_limit (β : α) : Prop := 
  (∃ γ, γ < β) ∧ (∀ γ < β, β ≠ succ γ)


theorem succ_of_not_zero_or_limit [Nonempty α]
  {β : α}
  (hz : β ≠ 0)
  (hl : ¬(is_limit β))
  : ∃ γ, γ < β ∧ β = succ γ := by
  by_contra ha
  push_neg at ha
  have _ : is_limit β := by
    constructor
    · use 0
      exact LE.le.lt_of_ne' (OrderBot.bot_le β) hz
    · assumption
  contradiction

theorem induction [Nonempty α]
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
    · have hs : ∃ γ, γ < μ ∧ μ = succ γ :=
        succ_of_not_zero_or_limit hz hlim
      rcases hs with ⟨γ, ⟨hi, hγ⟩⟩
      have h₁ : γ < μ := by
        by_contra hb
        push_neg at hb
        have hc : succ γ ≤ γ := by
          rw [← hγ]
          exact hb
        have _ : IsMax γ := max_of_succ_le hc
        have _ : ¬IsMax γ := not_isMax_of_lt hi
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

-- Proof: by induction on (WithTop α)

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

