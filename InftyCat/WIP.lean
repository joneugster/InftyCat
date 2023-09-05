import Mathlib.AlgebraicTopology.SimplicialSet
import Mathlib.AlgebraicTopology.SimplicialObject
import Mathlib.AlgebraicTopology.SimplexCategory

import Mathlib.CategoryTheory.LiftingProperties.Basic
import Mathlib

import InftyCat.LiftingProperty

open CategoryTheory

#check SSet


-- Retraction
#check retraction

/-
* Define Right/Left-Lifting-Property (as `MorphismProperty`): `LLP (L R)`, `RLP (L R)`

* Define Weak factorisation system. WFS: (L R : Set Morphisms(C))
 ```
 facObj {X Y : C} (f : X ⟶ Y) : C
 fac_left : X ⟶ facObj f
 facRight: facObj f ⟶ Y
 factorisation: ∀ f, f = facLeft ≫ facRight
 facLeft ∈ L, facRight ∈ R
 ```

 * Stability of retracts? -- Do we need that?




* Definition of functorial factorisation
* Small Object Argument
* Model structure



* Stability of RLP under pullback
-/

universe u

variable {M : Type u} [Category M]

#check MorphismProperty

/-- `LLP R` is a `MorphismProperty M` where a morphism `f` has this property iff
it has the Left-Lifting-Property (LLP) with respect to all morphisms `g` with
Morphism Property `R`. -/
def LLP (R : MorphismProperty M) : MorphismProperty M :=
  fun {A B} f =>
    ∀ {X Y : M} {g : X ⟶ Y} {a : A ⟶ X} {b : B ⟶ Y} (sq : CommSq a f g b), R g → sq.HasLift

/-- `RLP R` is a `MorphismProperty M` where a morphism `f` has this property iff
it has the Right-Lifting-Property (RLP) with respect to all morphisms `g` with
Morphism Property `R`. -/
def RLP (L : MorphismProperty M) : MorphismProperty M :=
  fun {X Y} g =>
    ∀ {A B : M} {f : A ⟶ B} {a : A ⟶ X} {b : B ⟶ Y} (sq : CommSq a f g b), L f → sq.HasLift

structure WeakFactorisationSystem (L R : MorphismProperty M) where
  h₁ : L = LLP R
  h₂ : R = RLP L
  facObj {X Y : M} (f : X ⟶ Y) : M
  facLeft {X Y : M} (f : X ⟶ Y) : X ⟶ facObj f
  facRight {X Y : M} (f : X ⟶ Y) : facObj f ⟶ Y
  comp {X Y : M} (f : X ⟶ Y) : facLeft f ≫ facRight f = f
  h₃ {X Y : M} (f : X ⟶ Y) : L (facLeft f)
  h₄ {X Y : M} (f : X ⟶ Y) : R (facRight f)

structure twoOutOfThree {X Y Z : M} (P : MorphismProperty M) where
  comp {f : X ⟶ Y} {g : Y ⟶ Z} : P f → P g → P (f ≫ g)
  left {f : X ⟶ Y} {g : Y ⟶ Z} : P g → P (f ≫ g) → P f
  right {f : X ⟶ Y} {g : Y ⟶ Z} : P f → P (f ≫ g) → P g

structure ModelCategory (C F W : MorphismProperty M) where
  p₁ : WeakFactorisationSystem (MorphismProperty.intersection C W) F




variable {C : Type u} [Category.{u} C] (L R : MorphismProperty C)


variable (X Y Z : C) (f : X ⟶ Y) (g : Y ⟶ Z) (hf : R f) (hg : R g)

variable (d : has2outOf3 R)

#check d.prop1

#check R f



#check WeakFactorisationSystem.facObj
