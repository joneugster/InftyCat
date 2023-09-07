import InftyCat.LiftingProperty.Basic
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Basic

import Mathlib.Init.Algebra.Order
import Mathlib.CategoryTheory.Category.Preorder

namespace CategoryTheory

set_option autoImplicit false

open Limits

universe u v

variable (C : Type u) [Category C]

#check IsWellOrder

/-- Unbundled version of WellOrder, with a successor function -/
class WellOrderUnbundled (α : Type v) extends LinearOrder α :=
  wo : IsWellOrder α (· < ·)

instance {α : Type v} [WellOrderUnbundled α] : SuccOrder α where
  succ := fun x => x -- x + 1 --TODO
  le_succ := sorry
  max_of_succ_le := sorry
  succ_le_of_lt := sorry
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

--instance : Preorder (Ordinal.toType α) := _

structure Chain (α : Type v) [WellOrderUnbundled α] where
  diag: α ⥤ C
  c : PreservesColimits diag
  ne : Nonempty α

structure Tower (α : Type v) [WellOrderUnbundled α] where
  diag : αᵒᵖ ⥤ C
  c : PreservesLimits diag
  ne : Nonempty α


namespace Chain

variable {C}
variable {α : Type v} [WellOrderUnbundled α]


open SuccOrder

-- dual should be Tower.target
def source (F : Chain C α) : C :=
  F.diag.obj 0

def atomicMap (F : Chain C α) (β : α) : F.diag.obj β ⟶ F.diag.obj (succ β) :=
  F.diag.map (homOfLE (le_succ β))

-- true iff every "atomic" map in F is in I
def generated_from (F : Chain C α) (I : MorphismProperty C) : Prop :=
  ∀ (β : α), (¬IsMax β) → I (atomicMap F β)


structure atomicCocone (F : Chain C α) (x : C) :=
  ι : ∀ (β : α), (F.diag.obj β) ⟶ x
  w : ∀ (β : α), ι β = (atomicMap F β) ≫ ι (succ β)

def getCocone {F : Chain C α} {x : C} (ac : atomicCocone F x)
  : Limits.Cocone F.diag where
    pt := x
    ι := {
      app := ac.ι
      naturality := fun {X Y} f => _
    }


structure compDiag (F : Chain C α) where
  c : Limits.Cocone F.diag
  ic : Limits.IsColimit c

-- The transfinite composition map given by a 'Chain.compDiag'
def comp {F : Chain C α} (G : compDiag F) : F.source ⟶ G.c.pt  :=
  G.c.ι.app 0


end Chain


namespace MorphismProperty

variable {C : Type u} [Category C]

-- Maybe change the universe level, TODO later
def StableUnderChainComposition (I : MorphismProperty C) : Prop :=
  ∀ (α : Type u) [WellOrderUnbundled α],
  ∀ (F : Chain C α),
    Chain.generated_from F I → ∀ (G : Chain.compDiag F), I (Chain.comp G)


#check Ordinal.inductionOn

theorem llp_chain_comp_stability (I : MorphismProperty C) :
  StableUnderChainComposition (leftLiftingProperty I) := by
  intro α αwos F hI G
  intro x y i hiI
  constructor
  intro v w sq
  constructor
  constructor
  -- ICI: commence la récurrence: on relève un par un les carrés
  -- Pour cela, le but est de construire un atomicCocone vers x,
  -- en construisant cette donnée par principe de récurrence
  -- (on peut sûrement même utiliser le principe de récurrence bien fondé)
  sorry

