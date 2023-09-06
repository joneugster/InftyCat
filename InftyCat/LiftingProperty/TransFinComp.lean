import InftyCat.LiftingProperty.Basic
import Mathlib.SetTheory.Ordinal.Basic

namespace CategoryTheory

namespace MorphismProperty

variable (C : Type u) [Category C]

#synth LinearOrder Ordinal
#check Ordinal.linearOrder

#synth Category Ordinal

variable (α : Ordinal)

-- Ordinals are Quotient of Well orders. This picks one and the underlying category:
#synth Category (Quotient.out α).α

structure transfiniteChain where
  F : (Quotient.out α).α ⥤ C
  proof : sorry -- F is cocontinuous / preserves colimits

structure transfiniteTower  where
  F : ((Quotient.out α).α)ᵒᵖ ⥤ C
  proof : sorry -- F is continuous / preserves limits

-- Take two `transfiniteChain` with `α < β` then

namespace transfiniteChain

variable {C}

#check Limits.Cocone -- TODO: What's a colimiting cocone

def extend {α β : Ordinal} (h : α ≤ β) (c : transfiniteChain C α)
    (d : transfiniteChain C β) : Prop :=
  sorry -- The functor `β ⥤ C` restricted to α extends `α ⥤ C`

structure comp (c : transfiniteChain C α) (d : transfiniteChain C (α + 1)) : Prop where
  p : extend (Ordinal.le_add_right α 1) c d
  -- colimCone: ColimitingCocone d

-- TODO: continue skeleton here.

#check Nonempty
