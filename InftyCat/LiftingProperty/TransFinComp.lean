import InftyCat.LiftingProperty.Basic
import Mathlib.SetTheory.Ordinal.Basic

import Mathlib.Init.Algebra.Order
import Mathlib.CategoryTheory.Category.Preorder

namespace CategoryTheory

variable (C : Type u) [Category C]


-- Ordinals are Quotient of Well orders. This picks one and the underlying
-- category: '(Quotient.out α).α'

structure Chain (α : Ordinal.{v}) where
  fonc : (Quotient.out α).α  ⥤ C
  proof : sorry -- F is cocontinuous / preserves colimits

structure Tower (α : Ordinal.{v})  where
  fonc : ((Quotient.out α).α)ᵒᵖ ⥤ C
  proof : sorry -- F is continuous / preserves limits


namespace Chain

variable {C}


def restr {α β : Ordinal} (h : α ≤ β) (F : Chain C β) : Chain C α :=
  sorry

def extend {α β : Ordinal} (h : α ≤ β) (F : Chain C α) (G : Chain C β) : Prop :=
  F = (restr h G)


def coconeOfSucc (α : Ordinal) (F : Chain C (α+1)) :
  Limits.Cocone (restr (Ordinal.le_add_right α 1) F).fonc :=
  sorry

structure compDiag {α : Ordinal} (F : Chain C α) where
  diag : Chain C (α+1)
  p : extend (Ordinal.le_add_right α 1) F diag
  ic : Limits.IsColimit (coconeOfSucc α diag)

-- Should be a map from G(0) -> G(alpha)
def comp {α : Ordinal} {F : Chain C α} (G : compDiag F) : Prop :=
  False

-- TODO: continue skeleton here.
