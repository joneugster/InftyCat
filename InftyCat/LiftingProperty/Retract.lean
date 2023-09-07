import InftyCat.LiftingProperty.Basic

-- TODO: Stability under retracts

namespace CategoryTheory

namespace MorphismProperty

variable {C : Type*} [Category C]

#check retraction

#check IsSplitMono

/-- `x` is a retract of `y` x ⟶ y ⟶ x = id_x -/
def IsRetractOf (x y : C) : Prop := ∃ (i : x ⟶ y), IsSplitMono i

-- TODO: Does it make sense to work in the Arrow category?
def retractMorphism' (f g : Arrow C) : Prop := IsRetractOf f g

def retractMorphism ⦃X Y Z W: C⦄ (f : X ⟶ Y) (g : Z ⟶ W) : Prop := IsRetractOf (Arrow.mk f) (Arrow.mk g)

variable (I : MorphismProperty C)


/--
 `RetractClass` takes a class of morphisms and returns a class of morphisms which are retracts of morphisms in the original class.
-/
def RetractClass : MorphismProperty C :=
  fun _ _ f => ∃ (Z W : C) (g : Z ⟶ W), I g ∧ retractMorphism f g

def StableUnderRetract : Prop :=
  ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (RetractClass I) f → I f

@[aesop forward safe]
lemma comsq_lemma {W X Y Z : C} (f : W ⟶ X) (g : W ⟶ Y) (h : X ⟶ Z) (i : Y ⟶ Z) (comsq: CommSq f g h i ) : 
f ≫ h = g ≫ i := comsq.w


--@[simp]
--@[aesop safe]
lemma comsq_lemma_alt {W X Y Z : C} (f : W ⟶ X) (g : W ⟶ Y) (h : X ⟶ Z) (i : Y ⟶ Z) :(CommSq f g h i ) ↔ (f ≫ h = g ≫ i) := by 
  constructor
  · intro commsq
    exact commsq.w
    --aesop_cat 
  · intro w 
    exact ⟨w⟩
  
theorem retract_stable_of_left_class : StableUnderRetract (leftLiftingProperty I) := 
by 
  intro A B f hrIf
  unfold RetractClass at hrIf
  rcases hrIf with ⟨C, D, g, hIg, hrg⟩  
  intro X Y i hIi 
  have : HasLiftingProperty g i := hIg i hIi
  rcases hrg with ⟨κ, ρ , hκρ⟩
  injection hκρ with hκρ₁ hκρ₂
  constructor
  · intro u v huv
    
    have horizontal_pasting : (ρ.left ≫ u) ≫ i  = g ≫ (ρ.right ≫ v) := by
      aesop 
    have H := HasLiftingProperty.sq_hasLift ⟨horizontal_pasting⟩ 
    rcases H with ⟨d, hd⟩ 
    let filler : B ⟶ X := κ.right ≫ d 
    refine {exists_lift := ?_}
    refine ⟨filler, ?_, ?_⟩   
    --let that: κ.right ≫ ρ.right = 𝟙 := by ext; 
    · calc 
        f ≫ filler = f ≫ κ.right ≫ d := by simp [hd]
        _          = κ.left ≫ g ≫ d := by simp [κ.w]  
        _          = κ.left ≫ ρ.left ≫ u  := by simp [hd]
        _          = u    := (reassoc_of% hκρ₁) u
    · calc 
        filler ≫ i = κ.right ≫ d ≫ i  := by simp
        _          = κ.right ≫ ρ.right ≫ v := by aesop_cat
        _          = v := (reassoc_of% hκρ₂) v




/- similar but use opposite category instead. -/
theorem solveMeToo' : StableUnderRetract (rightLiftingProperty I) := sorry

end MorphismProperty
end CategoryTheory
