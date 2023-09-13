/-
Copyright (c) 2023 Herman Rohrbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Herman Rohrbach, Jon Eugster, Sina ..., Marcus Nicolas, ...
-/

import Mathlib.CategoryTheory.LiftingProperties.Basic
import Mathlib.CategoryTheory.MorphismProperty

import InftyCat.LiftingProperty.Basic
import InftyCat.LiftingProperty.WeakFactorisationSystem


open CategoryTheory

/-Morphisms before objects in universes-/
universe v u

variable {𝓒 : Type u} [Category.{v} 𝓒]

class HasTwoOutOfSix (P : MorphismProperty 𝓒) : Prop where
  w {X Y Z W : 𝓒} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W} : P (f ≫ g) → P (g ≫ h) → (P (f ≫ g ≫ h) ∧ P f ∧ P g ∧ P h)

class HasTwoOutOfThree (P : MorphismProperty 𝓒) : Prop where
  comp {X Y Z : 𝓒} {f : X ⟶ Y} {g : Y ⟶ Z} : P f → P g → P (f ≫ g)
  left {X Y Z : 𝓒} {f : X ⟶ Y} {g : Y ⟶ Z} : P g → P (f ≫ g) → P f
  right {X Y Z : 𝓒} {f : X ⟶ Y} {g : Y ⟶ Z} : P f → P (f ≫ g) → P g

def TwoOutOfThreeFromSix {P : MorphismProperty 𝓒} (hP₁ : HasTwoOutOfSix P) (hP₂ : ∀ X : 𝓒, P (𝟙 X)) 
    : HasTwoOutOfThree P where
  comp := by
    intro X Y Z f g hf hg
    have hf : P (f ≫ 𝟙 Y) := by simp [hf, hP₂]
    have hg : P (𝟙 Y ≫ g) := by simp [hg, hP₂]
    let _ := hP₁.w hf hg
    aesop_cat
  left := by
    intro X Y Z f g hg hfg
    have hg : P (g ≫ 𝟙 Z) := by simp [hg, hP₂]
    let _ := hP₁.w hfg hg
    aesop_cat
  right := by
    intro X Y Z f g hf hfg
    have hf : P (𝟙 X ≫ f) := by simp [hf, hP₂]
    let _ := hP₁.w hf hfg
    aesop_cat

lemma two_out_of_three_from_six {P : MorphismProperty 𝓒} 
    : HasTwoOutOfSix P → (∀ X : 𝓒, P (𝟙 X)) → HasTwoOutOfThree P := by
  intro hP₁ hP₂
  exact TwoOutOfThreeFromSix hP₁ hP₂

/--
The class `CategoryWithWeakEqs` extends a `Category` and endows it with extra structure:
`we` is the class of weak equivalences, which contains all isomorphisms and satisfies two-out-of-three
-/
class CategoryWithWeakEqs (obj : Type u) extends Category.{v} obj : Type max u (v + 1) where
  we : MorphismProperty obj
  two_out_of_three : HasTwoOutOfThree we
  iso_is_we : MorphismProperty.isomorphisms obj ⊆ we

namespace CategoryWithWeakEqs

variable {𝓒 : Type u} [CategoryWithWeakEqs.{v} 𝓒]
variable {X Y Z W : 𝓒} (f : X ⟶ Y) (g : Y ⟶ Z)

/-The three basic lemmas for the two-out-of-three property-/

@[aesop safe]
lemma two_out_of_three_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
  we f → we g → we (f ≫ g) := by exact two_out_of_three.comp

@[aesop safe]
lemma two_out_of_three_left (f : X ⟶ Y) (g : Y ⟶ Z) :
  we g → we (f ≫ g) → we f := by exact two_out_of_three.left

@[aesop safe]
lemma two_out_of_three_right (f : X ⟶ Y) (g : Y ⟶ Z) :
  we f → we (f ≫ g) → we g := by exact two_out_of_three.right

end CategoryWithWeakEqs

/--
The class `ModelCategory` extends a `CategoryWithWeakEqs` and endows it with extra structure:
`cofib` is the class of cofibrations;
`fib` is the class of fibrations;
`wfs_accofib_fib` is the `WeakFactorisationSystem` with left class `cofib ∩ we` and right class `fib`; and
`wfs_cofib_acfib` is the `WeakFactorisationSystem` of `cofib` and `fib ∩ we`
-/
class ModelCategory (obj : Type u) extends CategoryWithWeakEqs.{v} obj : Type max u (v + 1) where
  cofib : MorphismProperty obj
  fib : MorphismProperty obj
  wfs_accofib_fib : WeakFactorisationSystem (cofib ∩ we) fib
  wfs_cofib_acfib : WeakFactorisationSystem cofib (fib ∩ we)

namespace ModelCategory

section Arrow

variable {M : Type u} [ModelCategory.{v} M]
variable {X Y Z W : M} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- Defines the acyclic cofibrations of the model structure
as those cofibrations that are also weak equivalences -/
def accofib : MorphismProperty M := cofib ∩ toCategoryWithWeakEqs.we

/-- Defines the acyclic fibrations of the model structure
as those fibrations that are also weak equivalences -/
def acfib : MorphismProperty M := fib ∩ toCategoryWithWeakEqs.we

/-Basic lemmas to go from acylic cofibrations and acyclic fibrations 
to cofibrations, fibrations and weak equivalences -/

/-To do: add attributes to use these lemmas in tactics, is `aesop safe` right? -/

@[aesop safe]
lemma cofib_from_accofib {f : X ⟶ Y}
    : accofib f → cofib f := by
  intro hf
  rcases hf with ⟨h, _⟩
  exact h

@[aesop safe]
lemma we_from_accofib {f : X ⟶ Y}
    : accofib f → toCategoryWithWeakEqs.we f := by
  intro hf
  rcases hf with ⟨_, h⟩
  exact h 

@[aesop safe]
lemma fib_from_acfib {f : X ⟶ Y}
    : acfib f → fib f := by
  intro hf
  rcases hf with ⟨h, _⟩
  exact h

@[aesop safe]
lemma we_from_acfib {f : X ⟶ Y}
    : acfib f → toCategoryWithWeakEqs.we f := by
  intro hf
  rcases hf with ⟨_, h⟩
  exact h 

end Arrow

section Lift

variable {M : Type u} [ModelCategory.{v} M]
variable {A B X Y : M} {i : A ⟶ B} {p : X ⟶ Y} {f : A ⟶ X} {g : B ⟶ Y}

/- Basic lemmas to construct lifts in commutative squares in model categories -/

/--
Shows that a commutative square
```
A -- f -> X
|         |
i         p
|         |
B -- g -> Y
```
has a lift `B ⟶ X` making the upper left and lower right triangle commute,
whenever `i` is an acyclic cofibration and `p` is a fibration
-/
lemma hasLift_accofib_fib (sq : CommSq f i p g) 
    : accofib i → fib p → CommSq.HasLift sq := by
  intro hi hp
  let h := wfs_accofib_fib.hasLift sq
  exact h hi hp

/--
Constructs a `LiftStruct` for a commutative square whose left arrow `i` is an acyclic cofibration
and whose right arrow `p` is a fibration
-/
noncomputable def lift_accofib_fib (sq : CommSq f i p g) (hi : accofib i) (hp : fib p) 
    : CommSq.LiftStruct sq :=
  (hasLift_accofib_fib sq hi hp).exists_lift.some

/--
Shows that a commutative square
```
A -- f -> X
|         |
i         p
|         |
B -- g -> Y
```
has a lift `B ⟶ X` making the upper left and lower right triangle commute,
whenever `i` is a cofibration and `p` is an acyclic fibration
-/
lemma hasLift_cofib_acfib (sq : CommSq f i p g)
    : cofib i → acfib p → CommSq.HasLift sq := by
  intro hi hp
  let h := wfs_cofib_acfib.hasLift sq
  exact h hi hp

/--
Constructs a `LiftStruct` for a commutative square whose left arrow `i` is a cofibration
and whose right arrow `p` is an acyclic fibration
-/
noncomputable def lift_cofib_acfib (sq : CommSq f i p g) (hi : cofib i) (hp : acfib p) 
    : CommSq.LiftStruct sq :=
  (hasLift_cofib_acfib sq hi hp).exists_lift.some

end Lift
