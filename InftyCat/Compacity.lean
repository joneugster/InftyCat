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


class Limits.HasStronglyDirectedColimitsOfSize
  {C : Type u} [Category C]
  (κ : Cardinal.{v})
  : Prop where
  has_strongly_directed_colimits :
    ∀ (I : Type w) [PartialOrder I] [PartialOrder.IsStronglyDirected I κ],
      CategoryTheory.Limits.HasColimitsOfShape I C

#check Limits.IsColimit
#check Limits.colimit.desc

-- Construct the Cocone Hom(x, F(-))


/- Did not find this construction in Mathlib..., it is whiskering, but not
   in the same direction as 'Cocone.whisker' -/
def Limits.Cocone.eval
  {I : Type*} [Category I]
  {C : Type*} [Category C]
  {D : Type*} [Category D]
  {F : I ⥤ C}
  (c : Limits.Cocone F)
  (G : C ⥤ D)
  : Limits.Cocone (F ⋙ G) :=
  {
    pt := G.obj (c.pt)
    ι := (c.ι ◫ (NatTrans.id G)) ≫ (Functor.constComp I c.pt G).hom
  }



def Limits.Cocone.mapColimHom
  {I : Type*} [Category I]
  {C : Type*} [Category C]
  {F : I ⥤ C}
  (x : C)
  (c : Limits.Cocone F)
  {hc : Limits.Cocone (F ⋙ coyoneda.obj (Opposite.op x))}
  (ihc : Limits.IsColimit hc)
  (a: hc.pt)
  :  x ⟶ c.pt  :=
  -- Limits.Cocone.eval c (F ⋙ coyoneda.obj (Opposite.op x))
  sorry -- TODO


-- It is important to make use of universes u v w when using this class
class IsCompact
  {C : Type u} [Category C]
  (x : C)
  (κ : Cardinal.{v}) [Limits.HasStronglyDirectedColimitsOfSize (C := C) κ]
  : Prop where
    bij :
      ∀ (I : Type w) [PartialOrder I] [PartialOrder.IsStronglyDirected I κ],
      ∀ (F : I ⥤ C),
      ∀ (c : Limits.Cocone F),
      ∀ (hc : Limits.Cocone (F ⋙ coyoneda.obj (Opposite.op x))),
      ∀ (ihc : Limits.IsColimit hc),
        Limits.IsColimit c →
          Function.Bijective (Limits.Cocone.mapColimHom x c ihc)
