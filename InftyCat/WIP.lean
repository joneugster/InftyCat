import Mathlib.AlgebraicTopology.SimplicialSet
import Mathlib.AlgebraicTopology.SimplicialObject
import Mathlib.AlgebraicTopology.SimplexCategory

import Mathlib.CategoryTheory.LiftingProperties.Basic
import Mathlib

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

def LLP (R : MorphismProperty M) : MorphismProperty M := sorry
def RLP (L : MorphismProperty M) : MorphismProperty M := sorry


structure WeakFactorisationSystem (L R : MorphismProperty M) where
  h₁ : L = LLP R
  h₂ : R = RLP L
  facObj {X Y : M} (f : X ⟶ Y) : M
  facLeft {X Y : M} (f : X ⟶ Y) : X ⟶ facObj f
  facRight {X Y : M} (f : X ⟶ Y) : facObj f ⟶ Y
  comp {X Y : M} (f : X ⟶ Y) : facLeft f ≫ facRight f = f
  h₃ {X Y : M} (f : X ⟶ Y) : L (facLeft f)
  h₄ {X Y : M} (f : X ⟶ Y) : R (facRight f)

def MorphismProperty.intersection (A B : MorphismProperty M) : MorphismProperty M :=
  fun X Y f => A f ∧ B f

-- def MorphismProperty.2outOf3 (A : MorphismProperty M) : Prop :=
--   fun X Y f => A f ∧ B f
--   fun X Y f, Y Z g


structure ModelCategory (C F W : MorphismProperty M) where



variable {C : Type u} [Category.{u} C] (L R : MorphismProperty C)

variable (X Y : C) (f : X ⟶ Y)

variable (R : MorphismProperty C)

#check R f



#check WeakFactorisationSystem.facObj