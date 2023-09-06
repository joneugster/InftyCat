import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.CategoryTheory.Limits.Filtered

import Mathlib.Init.Algebra.Order

open CategoryTheory

-- Not sure about this name
def StronglyDirected {α : Type u} {ι : Sort v}
  (rel : α → α → Prop) (f : ι → α) (κ : Cardinal.{w}) :=
  ∀ σ, Cardinal.mk σ < κ → (∀ g : σ → ι, ∃ m, ∀ x, rel (f (g x)) m)

def PartialOrder.stronglyDirected
  (I : Type u) [h : PartialOrder I]
  (κ : Cardinal.{v}) : Prop :=
  StronglyDirected h.toLE.le id κ

class PartialOrder.IsStronglyDirected
  (I : Type u) [PartialOrder I]
  (κ : Cardinal.{v})
  : Prop where
  directed : PartialOrder.stronglyDirected I κ


variable {C : Type u} [Category C]

class CategoryTheory.Limits.HasStronglyDirectedColimitsOfSize
  (κ : Cardinal.{v})
  : Prop where
  has_strongly_directed_colimits :
    ∀ (I : Type w) [PartialOrder I] [PartialOrder.IsStronglyDirected I κ],
      CategoryTheory.Limits.HasColimitsOfShape I C

structure IsSmall (x : C) (κ : Cardinal.{v})
  [CategoryTheory.Limits.HasStronglyDirectedColimitsOfSize (C := C) κ] where
  -- TODO: bijection of the comparisons maps between hom sets A.22

