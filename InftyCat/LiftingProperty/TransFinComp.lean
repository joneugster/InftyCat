import InftyCat.LiftingProperty.Basic
import Mathlib.SetTheory.Ordinal.Basic

namespace CategoryTheory

variable (C : Type u) [Category C]

#synth LinearOrder Ordinal
#check Ordinal.linearOrder

#synth Category Ordinal

variable (α : Ordinal)

-- Ordinals are Quotient of Well orders. This picks one and the underlying category:
#synth Category (Quotient.out α).α

structure Chain where
  fonc : (Quotient.out α).α ⥤ C
  proof : sorry -- F is cocontinuous / preserves colimits

structure Tower  where
  fonc : ((Quotient.out α).α)ᵒᵖ ⥤ C
  proof : sorry -- F is continuous / preserves limits


namespace Chain

variable {C}-- TODO: What's a colimiting cocone


def restr {α β : Ordinal} (h : α ≤ β) (F : Chain C β) : Chain C α :=
  sorry

def extend {α β : Ordinal} (h : α ≤ β) (F : Chain C α) (G : Chain C β) : Prop :=
  F = (restr h G)


def coconeOfSucc (α : Ordinal) (F : Chain C (α+1)) :
  Limits.Cocone (restr (Ordinal.le_add_right α 1) F).fonc :=
  sorry

structure compDiag (F : Chain C α) where
  diag : Chain C (α+1)
  p : extend (Ordinal.le_add_right α 1) F diag
  ic : Limits.IsColimit (coconeOfSucc α diag)

-- Should be a map from G(0) -> G(alpha)
def comp {F : Chain C α} (G : compDiag F) :
  sorry

-- TODO: continue skeleton here.

#check Nonempty
