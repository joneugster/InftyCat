import Mathlib.CategoryTheory.MorphismProperty

import InftyCat.LiftingProperty.Basic

open CategoryTheory

universe v u

variable {𝓒 : Type u} [Category.{v} 𝓒]

/--
The datum of a factorisation of a morphism `f : X ⟶ Y` into a composition of two morphisms 
`l : X ⟶ fac_obj` and `r : fac_obj ⟶ Y`
having property `L` and `R`, respectively
-/
structure FactorStruct {X Y : 𝓒} (L R : MorphismProperty 𝓒) (f : X ⟶ Y) where 
  fac_obj : 𝓒
  l : X ⟶ fac_obj
  r : fac_obj ⟶ Y
  hl : L l
  hr : R r
  comp : l ≫ r = f

class WeakFactorisationSystem (L R : MorphismProperty 𝓒) : Type max u v where
  llp : L = leftLiftingProperty R
  rlp : R = rightLiftingProperty L
  exists_fac {X Y : 𝓒} (f : X ⟶ Y) : Nonempty (FactorStruct L R f)

namespace WeakFactorisationSystem

variable {A B X Y : 𝓒} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y} {L R : MorphismProperty 𝓒}
variable [wfs : WeakFactorisationSystem L R]

noncomputable def factorisation (f : X ⟶ Y) 
    : FactorStruct L R f := (exists_fac f).some

lemma left_contains_isos : MorphismProperty.isomorphisms 𝓒 ⊆ L := by
  intro A B i hi
  have _ : IsIso i := by apply hi
  let j := inv i
  let h := wfs.llp
  simp [h, leftLiftingProperty]
  intro X Y p _
  constructor
  intro f g sq
  constructor
  constructor
  use j ≫ f
  · aesop_cat
  · rw [Category.assoc, sq.w]
    aesop_cat

lemma right_contains_isos : MorphismProperty.isomorphisms 𝓒 ⊆ R := by
  intro X Y r hr
  have _ : IsIso r := by apply hr
  let s := inv r
  let h := wfs.rlp
  simp [h, rightLiftingProperty]
  intro X Y i _ 
  constructor
  intro f g sq
  constructor
  constructor
  use g ≫ s
  · rw [← Category.assoc, sq.w.symm]
    aesop_cat
  · aesop_cat  

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
whenever `L` and `R` form a weak factorisation system and `i` is in `L` 
and `p` in `R`
 -/
noncomputable def hasLift (sq : CommSq f i p g) (hi : L i) (hp : R p) 
    : CommSq.HasLift sq := by
  have hL := wfs.llp
  have hi : (leftLiftingProperty R) i := by aesop_cat
  have hip : HasLiftingProperty i p := by exact hi p hp    
  exact HasLiftingProperty.sq_hasLift sq

/--
Extracts a `LiftStruct` from a commutative square
```
A -- f -> X
|         |
i         p
|         |
B -- g -> Y
```
with `i` in `L` and `p` in `R` whenever `L` and `R` form a `WeakFactorisationSystem`
-/
noncomputable def liftStruct (sq : CommSq f i p g) (hi : L i) (hp : R p) 
    : CommSq.LiftStruct sq := (hasLift sq hi hp).exists_lift.some

end WeakFactorisationSystem
