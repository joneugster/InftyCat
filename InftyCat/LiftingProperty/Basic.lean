import Mathlib.CategoryTheory.MorphismProperty
import Mathlib.CategoryTheory.LiftingProperties.Basic

namespace CategoryTheory

universe u

variable {C : Type u} [Category C]

namespace MorphismProperty

/-- The class of morphisms in `C` that satisfy both properties. -/
def intersection (A B : MorphismProperty C) : MorphismProperty C :=
  fun _ _ f => A f ∧ B f

/- implies A B hold iff having property A for a morphism f implies
   property B for f -/
def implies (A B : MorphismProperty C) : Prop :=
  ∀ x y, ∀ (f : x ⟶ y),  A f → B f

end MorphismProperty

/-- `leftLiftingProperty I` is a `MorphismProperty C` where a morphism `f` has this property iff
it has the Left-Lifting-Property (LLP) with respect to all morphisms `i` with
Morphism Property `I`. -/
def leftLiftingProperty (I : MorphismProperty C) : MorphismProperty C :=
  fun _ _ f => ∀ {x y} (i : x ⟶ y), I i → HasLiftingProperty f i

/-- `rightLiftingProperty I` is a `MorphismProperty M` where a morphism `g` has this property iff
it has the Right-Lifting-Property (RLP) with respect to all morphisms `i` with
Morphism Property `I`. -/
def rightLiftingProperty (I : MorphismProperty C) : MorphismProperty C :=
  fun _ _ g => ∀ {x y} (i : x ⟶ y), I i → HasLiftingProperty i g

theorem opLLP (I : MorphismProperty C) :
    (rightLiftingProperty I.op).unop = leftLiftingProperty I := by
  simp [leftLiftingProperty, rightLiftingProperty]
  funext x y f  
  ext
  constructor
  · intro hl a b i hi
    apply HasLiftingProperty.unop
    apply hl
    assumption
  · intro hr a_op b_op i_op hi_op
    apply HasLiftingProperty.op
    apply hr
    assumption  

#check HasLiftingProperty.iff_op

class HasLeftLiftingProperty {x y : C} (I : MorphismProperty C) (f : x ⟶ y) : Prop where
  lift : (leftLiftingProperty I) f

class HasRightLiftingProperty {x y : C} (I : MorphismProperty C) (g : x ⟶ y) : Prop where
  lift : (rightLiftingProperty I) g

theorem op_of_LLPisRRP {x y : C} (I : MorphismProperty C) (f : x ⟶ y) : 
    HasLeftLiftingProperty I.op f.op ↔ HasRightLiftingProperty I f := by
  constructor
  · intro h
    rcases h with ⟨lift⟩ 
    constructor
    unfold leftLiftingProperty at lift
    intro a b i hi
    specialize lift i.op
    apply HasLiftingProperty.unop
    apply lift
    simpa
  · intro h
    rcases h with ⟨lift⟩ 
    constructor
    unfold rightLiftingProperty at lift
    intro a b i hi
    specialize lift i.unop
    apply HasLiftingProperty.op
    apply lift
    simpa

/- This result makes it possible for us to dualize results on classes rlp(I)
   to results on classes llp(I) -/
#check HasLiftingProperty.op

namespace HasRightLiftingProperty

instance of_iso {x y : C} (i : x ⟶ y) (I : MorphismProperty C) [IsIso i] :
    HasRightLiftingProperty I i := ⟨ by
  rw [rightLiftingProperty]
  intro z w f _
  exact HasLiftingProperty.of_right_iso f i ⟩

instance of_comp {x y z : C} (f : x ⟶ y) (g : y ⟶ z)
    (I : MorphismProperty C) [fRlp: HasRightLiftingProperty I f]
    [gRlp: HasRightLiftingProperty I g] : HasRightLiftingProperty I (f ≫ g) := ⟨ by
  rw [rightLiftingProperty]
  intro z w i hiI
  have := (fRlp.lift i hiI)
  have := (gRlp.lift i hiI)
  exact HasLiftingProperty.of_comp_right i f g ⟩

end HasRightLiftingProperty

namespace HasLeftLiftingProperty

instance of_iso {x y : C} (i : x ⟶ y) (I : MorphismProperty C) [IsIso i] :
    HasLeftLiftingProperty I i := ⟨ by
  rw [leftLiftingProperty]
  intro z w f _
  exact HasLiftingProperty.of_left_iso i f ⟩

instance of_comp {x y z : C} (f : x ⟶ y) (g : y ⟶ z)
    (I : MorphismProperty C) [fRlp: HasRightLiftingProperty I f]
    [gRlp: HasRightLiftingProperty I g] : HasRightLiftingProperty I (f ≫ g) := ⟨ by
  rw [rightLiftingProperty]
  intro z w i hiI
  have := (fRlp.lift i hiI)
  have := (gRlp.lift i hiI)
  exact HasLiftingProperty.of_comp_right i f g ⟩

end HasLeftLiftingProperty


-- Stability properties

-- def Stab




-- Lemma: relate llp(I) and rlp(op(I))
