import InftyCat.LiftingProperty.Basic
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Basic

import Mathlib.Init.Algebra.Order
import Mathlib.CategoryTheory.Category.Preorder

namespace CategoryTheory

open Limits

variable (C : Type u) [Category C]



-- Unbundled version of WellOrder, with a successor function
class WellOrderSucc (α : Type v) extends LinearOrder α, SuccOrder α :=
  wo : IsWellOrder α (· < ·)


def WellOrderSucc.bundle (α : Type v) [h : WellOrderSucc α]
  : WellOrder.{v} where
  α := α
  r := (· < · )
  wo := h.wo




def WellOrderSucc.zero (α : Type v) [WellOrderSucc α]
  (ne : Nonempty α) : α :=
  sorry

def WellOrderSucc.zero (α : Type v) [WellOrderSucc α]
  (ne : Nonempty α) : α :=
  sorry

def WellOrderSucc.initial (α : Type v) [WellOrderSucc α] (β : α) :=
  {γ : α // γ < β}

-- We still have a well founded order by restricting it
instance WellOrderSucc.ofInitial (α : Type v) [WellOrderSucc α] (β : α)
  : WellOrderSucc (WellOrderSucc.initial α β) :=
  sorry

--instance : Preorder (Ordinal.toType α) := _

structure Chain (α : Type v) [WellOrderSucc α] where
  diag: α ⥤ C
  c : PreservesColimits diag
  ne : Nonempty α

structure Tower (α : Type v) [WellOrderSucc α] where
  diag : αᵒᵖ ⥤ C
  c : PreservesLimits diag
  ne : Nonempty α


namespace Chain

variable {C}
variable {α : Type v} [αwos : WellOrderSucc α]

-- dual should be Tower.target
def source (F : Chain C α) : C :=
  F.diag.obj (WellOrderSucc.zero α F.ne)


def atomicMap (F : Chain C α) (β : α)
  : F.diag.obj β ⟶ F.diag.obj (αwos.succ β) :=
  F.diag.map (homOfLE (αwos.le_succ β))

-- true iff every "atomic" map in F is in I
def generated_from (F : Chain C α) (I : MorphismProperty C) : Prop :=
  ∀ (β : α), (¬IsMax β) → I (atomicMap F β)


structure atomicCocone (F : Chain C α) (x : C) :=
  ι : ∀ (β : α), (F.diag.obj β) ⟶ x
  w : ∀ (β : α), ι β = (atomicMap F β) ≫ ι (αwos.succ β)

def getCocone {F : Chain C α} {x : C} (ac : atomicCocone F x)
  : Limits.Cocone F.diag where
    pt := x
    ι := {
      app := ac.ι
      naturality := sorry
    }


structure compDiag (F : Chain C α) where
  c : Limits.Cocone F.diag
  ic : Limits.IsColimit c

-- The transfinite composition map given by a 'Chain.compDiag'
def comp {F : Chain C α} (G : compDiag F) : F.source ⟶ G.c.pt  :=
  G.c.ι.app (WellOrderSucc.zero α F.ne)


end Chain


namespace MorphismProperty

variable {C : Type u} [Category C]

-- Maybe change the universe level, TODO later
def StableUnderChainComposition (I : MorphismProperty C) : Prop :=
  ∀ (α : Type u) [WellOrderSucc α],
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


-- TODO: continue skeleton here.
