import Mathlib.CategoryTheory.MorphismProperty
import Mathlib.CategoryTheory.LiftingProperties.Basic

open CategoryTheory

universe u

variable {C : Type u} [Category C]

def MorphismProperty.intersection (A B : MorphismProperty C)
  : MorphismProperty C :=
  fun _ _ f => A f ∧ B f

/- implies A B hold iff having property A for a morphism f implies
   property B for f -/
def MorphismProperty.implies (A B : MorphismProperty C) : Prop :=
  ∀ x y, ∀ (f : x ⟶ y),  A f → B f

def leftLiftingProperty (I : MorphismProperty C) : MorphismProperty C :=
  fun _ _ f =>
    ∀ x y, ∀ (i : x ⟶ y), I i → HasLiftingProperty f i

def rightLiftingProperty (I : MorphismProperty C) : MorphismProperty C :=
  fun _ _ f =>
    ∀ x y, ∀ (i : x ⟶ y), I i → HasLiftingProperty i f


class HasLeftLiftingProperty {x y: C} (I : MorphismProperty C) (f : x ⟶ y)
  : Prop where
  lift : (leftLiftingProperty I) f

class HasRightLiftingProperty {x y: C} (I : MorphismProperty C) (f : x ⟶ y)
  : Prop where
  lift : (rightLiftingProperty I) f


def has_llp (A B : MorphismProperty C) : Prop :=
  MorphismProperty.implies A (leftLiftingProperty B)

def has_rlp (A B : MorphismProperty C) : Prop :=
  MorphismProperty.implies A (rightLiftingProperty B)

/- This result makes it possible for us to dualize results on classes rlp(I)
   to results on classes llp(I) -/
#check HasLiftingProperty.op

instance HasRightLiftingProperty.of_iso {x y : C} (i : x ⟶ y)
  (I : MorphismProperty C) [IsIso i]
  : HasRightLiftingProperty I i := ⟨
    by
      rw [rightLiftingProperty]
      intro z
      intro w
      intro f
      intro _
      exact HasLiftingProperty.of_right_iso f i
  ⟩

instance HasRightLiftingProperty.of_comp {x y z: C} (f : x ⟶ y) (g : y ⟶ z)
  (I : MorphismProperty C)
  [fRlp: HasRightLiftingProperty I f]
  [gRlp: HasRightLiftingProperty I g]
  : HasRightLiftingProperty I (f ≫ g) := ⟨
    by
      rw [rightLiftingProperty]
      intro z
      intro w
      intro i
      intro hiI
      exact @HasLiftingProperty.of_comp_right _ _ _ _ _ _ _ i f g
        (fRlp.lift z w i hiI) (gRlp.lift z w i hiI)    
  ⟩


-- Lemma: relate llp(I) and rlp(op(I))
