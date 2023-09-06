import Mathlib.AlgebraicTopology.SimplicialSet
import Mathlib.AlgebraicTopology.SimplicialObject
import Mathlib.AlgebraicTopology.SimplexCategory

import Mathlib.CategoryTheory.LiftingProperties.Basic
import Mathlib

import InftyCat.LiftingProperty.Basic

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

structure WeakFactorisationSystem (L R : MorphismProperty M) where
  h₁ : L = leftLiftingProperty R
  h₂ : R = rightLiftingProperty L
  facObj {X Y : M} (f : X ⟶ Y) : M
  facLeft {X Y : M} (f : X ⟶ Y) : X ⟶ facObj f
  facRight {X Y : M} (f : X ⟶ Y) : facObj f ⟶ Y
  comp {X Y : M} (f : X ⟶ Y) : facLeft f ≫ facRight f = f
  h₃ {X Y : M} (f : X ⟶ Y) : L (facLeft f)
  h₄ {X Y : M} (f : X ⟶ Y) : R (facRight f)

structure twoOutOfThree (P : MorphismProperty M) where
  comp {X Y Z : M} {f : X ⟶ Y} {g : Y ⟶ Z} : P f → P g → P (f ≫ g)
  left {X Y Z : M} {f : X ⟶ Y} {g : Y ⟶ Z} : P g → P (f ≫ g) → P f
  right {X Y Z : M} {f : X ⟶ Y} {g : Y ⟶ Z} : P f → P (f ≫ g) → P g

structure ModelCategory (C F W : MorphismProperty M) where
  p₁ : WeakFactorisationSystem (MorphismProperty.intersection C W) F
  p₂ : WeakFactorisationSystem C (MorphismProperty.intersection F W)
  p₃ : twoOutOfThree W


-- TODO
-- /-- We can skip checking the condition C ∩ W ⊆ AC. Compare Hirschhorn, Theorem 11.3.1. -/
-- -- TODO: we can also omit "AC ⊆ C" because it follows from AF ⊆ F, right?
-- lemma is_model_category.mk' {W C AF AC F : morphism_class M}
--   (weq : is_weak_equivalences W)
--   (caf : is_wfs C AF) (acf : is_wfs AC F)
--   (hAF : AF = F ∩ W) (hAC : AC ⊆ W) :
--   is_model_category W C F := sorry

/-

M1-4 of Quillen


TODO:
* Prove retracts
*
* Examples of Model Categories: Small object argument
* General Results:
-/


variable {C : Type u} [Category.{u} C] (L R : MorphismProperty C)

variable (X Y Z : C) (f : X ⟶ Y) (g : Y ⟶ Z) (hf : R f) (hg : R g)

variable (d : has2outOf3 R)

#check d.prop1

#check R f



#check WeakFactorisationSystem.facObj


