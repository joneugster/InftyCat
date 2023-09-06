import InftyCat.LiftingProperty.Basic
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Basic

import Mathlib.Init.Algebra.Order
import Mathlib.CategoryTheory.Category.Preorder

namespace CategoryTheory

open Limits

variable (C : Type u) [Category C]


variable (o : Ordinal.{v})
#check (Quotient.out o).α



-- Ordinals are Quotient of Well orders. This picks one and the underlying
-- category: '(Quotient.out α).α'

-- def Ordinal.toType (α : Ordinal.{v}) : Type (v + 1) :=
--   {β : Ordinal.{v} // β < α}

def Ordinal.toType : Type (v+1) := FullSubcategory (· < o)

-- example (α β : Ordinal.{v}) (h : α < β) := sorry

-- #check ordinalAsCategory o

instance : Coe Ordinal.{v} (Type (v+1)) := ⟨ fun α => Ordinal.toType α ⟩

--#check InducedCategory (Ordinal.{v}) (fun (β : Ordinal.toType o) => (β : Type (u+1)))

#check Ordinal.toType

class WellFoundedOrder (α : Type v) extends LinearOrder α, IsWellFounded α (· ≤ ·) where

--instance : Preorder (Ordinal.toType α) := _

structure Chain (α : Type v) [WellFoundedOrder α] where
  F : α ⥤ C
  proof : PreservesColimits F

structure Tower (α : Type v) [WellFoundedOrder α] where
  F : αᵒᵖ ⥤ C
  proof : PreservesLimits F


namespace Chain

variable {C}

def funcOrdCat {α β : Ordinal} (h : α ≤ β) :
  ((Quotient.out α).α) ⥤ (Quotient.out β).α :=
  sorry


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
