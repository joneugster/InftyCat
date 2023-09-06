import InftyCat.LiftingProperty.Basic

-- TODO: Stability under retracts

namespace CategoryTheory

namespace MorphismProperty

variable {C : Type*} [Category C]

#check retraction

#check IsSplitMono

def retract (x y : C) : Prop := ∃ (i : x ⟶ y), IsSplitMono i

-- TODO: Does it make sense to work in the Arrow category?
def retractMorphism' (f g : Arrow C) : Prop := retract f g

def retractMorphism ⦃X Y Z W: C⦄ (f : X ⟶ Y) (g : Z ⟶ W) : Prop := retract (Arrow.mk f) (Arrow.mk g)

variable (I : MorphismProperty C)

def IsRetract : MorphismProperty C :=
  fun _ _ f => ∃ (Z W : C) (g : Z ⟶ W), I g ∧ retractMorphism f g

def StableUnderRetract : Prop :=
  ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (IsRetract I) f → I f

theorem solveMeToo : StableUnderRetract (leftLiftingProperty I) := sorry

theorem solveMeToo' : StableUnderRetract (rightLiftingProperty I) := sorry
