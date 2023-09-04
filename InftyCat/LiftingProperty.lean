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
    ∀ x y, ∀ (u : x ⟶ y), I u → HasLiftingProperty f u

def rightLiftingProperty (I : MorphismProperty C) : MorphismProperty C :=
  fun _ _ f =>
    ∀ x y, ∀ (u : x ⟶ y), I u → HasLiftingProperty u f

def HasLeftLiftingProperty (A B : MorphismProperty C) : Prop :=
  MorphismProperty.implies A (leftLiftingProperty B)

def HasRightLiftingProperty (A B : MorphismProperty C) : Prop :=
  MorphismProperty.implies A (rightLiftingProperty B)

/- Maybe change the name: the lemma says that f has the llp relatively to g
  iff op(g) has the llp relatively to op(f)
  This result makes it possible for us to dualize results on classes rlp(I)
  to results on classes llp(I)
 -/
lemma LiftingProperties.lift_op {x y z w : C} (f : x ⟶ y) (g: z ⟶ w)
  : (HasLiftingProperty f g) ↔ (HasLiftingProperty g.op f.op) :=
  sorry


lemma iso_rlp {x y : C} (f : x ≅ y) (I : MorphismProperty C)
  : (rightLiftingProperty I) f.hom :=
  sorry

lemma comp_rlp {x y z : C} (f : x ⟶ y) (g : y ⟶ z) (I : MorphismProperty C)
  : (rightLiftingProperty I) (f ≫ g) :=
  sorry

-- Lemma: relate llp(I) and rlp(op(I))
