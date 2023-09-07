import InftyCat.LiftingProperty.Basic
import InftyCat.Basics.Pushout
import ProofWidgets.Component.GoalTypePanel

-- TODO: Stability of pullbacks and pushouts

namespace CategoryTheory

open Limits

namespace MorphismProperty

-- LLP is stable under pushout
#check StableUnderCobaseChange

variable {C : Type*} [Category C] (L R : MorphismProperty C)

  structure DoubleCommSq {A₁ A₂ A₃ B₁ B₂ B₃ : C} (a₁ : A₁ ⟶ A₂) (a₂ : A₂ ⟶ A₃) (b₁ : B₁ ⟶ B₂) (b₂ : B₂ ⟶ B₃)
      (f₁: A₁ ⟶ B₁) (f₂: A₂ ⟶ B₂) (f₃: A₃ ⟶ B₃) where
    leftSquareCommutes : CommSq a₁ f₁ f₂ b₁
    rightSquareCommutes : CommSq a₂ f₂ f₃ b₂

  namespace DoubleCommSq

  variable {A₁ A₂ A₃ B₁ B₂ B₃ : C} {a₁ : A₁ ⟶ A₂} {a₂ : A₂ ⟶ A₃} {b₁ : B₁ ⟶ B₂} {b₂ : B₂ ⟶ B₃}
      {f₁: A₁ ⟶ B₁} {f₂: A₂ ⟶ B₂} {f₃: A₃ ⟶ B₃}

  theorem outerSquareCommutes (dsq : DoubleCommSq a₁ a₂ b₁ b₂ f₁ f₂ f₃) : CommSq (a₁ ≫ a₂) f₁ f₃ (b₁ ≫ b₂) := by
    have lsq := dsq.leftSquareCommutes.w
    have rsq := dsq.rightSquareCommutes.w 
    have target : CommSq (a₁ ≫ a₂) f₁ f₃ (b₁ ≫ b₂) := {
      w := by
        simp [rsq]
        rw [← Category.assoc]
        simp [lsq]
    }
    exact target

  structure CommTr {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) : Prop where
    -- The triangle commutes
    w : f ≫ g = h

  theorem upperTriangle (sq : CommSq a₁ f₁ f₂ b₁) : CommTr a₁ f₂ (f₁ ≫ b₁) := by
    have tr : CommTr a₁ f₂ (f₁ ≫ b₁) := {
      w := by exact sq.w
    }
    exact tr

  theorem lowerTriangle (sq : CommSq a₁ f₁ f₂ b₁) : CommTr f₁ b₁ (a₁ ≫ f₂) := by
    exact (upperTriangle sq.flip)

  end DoubleCommSq

  theorem llpIsStableUnderCobaseChange : StableUnderCobaseChange (leftLiftingProperty R) := by
    with_panel_widgets [ProofWidgets.GoalTypePanel]
      -- Unpack the definition of being stable under cobase change (pushout) and introduce an arbitrary pushout
      simp [StableUnderCobaseChange]
      intro A B A' B' l₁ a₁ l₂ b₁ hB' hl₁
      let sq₁ := hB'.toCommSq
      let pushout := hB'.isColimit'.some
      -- Unpack the definition of the left lifting property and introduce an arbitrary lifting diagram
      simp [leftLiftingProperty]
      intro A'' B'' r hr
      -- Note that since `l₁` has the left lifting property against `R` and `r` is in `R`, 
      -- it has lifts against `r`
      specialize hl₁ r hr
      constructor
      intro a₂ b₂ sq₂
      -- Construct the outer commutative square
      let sq₃ : CommSq (a₁ ≫ a₂) l₁ r (b₁ ≫ b₂) := {
        w := by 
          let dsq : DoubleCommSq a₁ a₂ b₁ b₂ l₁ l₂ r := {
            leftSquareCommutes := by exact sq₁
            rightSquareCommutes := by exact sq₂
          }
          exact dsq.outerSquareCommutes.w
      }
      -- The outer square `sq₃` has a lift because of `hl₁`, so we construct a LiftStruct `h`, 
      -- containing the lift `h.l` and the commutativity of the two triangles
      have hsq₃ := HasLiftingProperty.sq_hasLift sq₃
      let h := hsq₃.exists_lift.some
      -- To show that `sq₂` has a lift, we call `constructor` on it to reduce to the
      -- statement that its `LiftStruct` is nonempty
      constructor
      -- We define `h'` as the universal map from `pushout` to `A''`, and `use` it as a tactic to
      -- show that `LiftStruct` is nonempty, i.e. we verify that it satisfies the necessary properties
      let h' : B' ⟶ A'' := PushoutCocone.IsColimit.desc pushout a₂ h.l h.fac_left.symm
      -- The upper triangle in `sq₂` given by `h'` commutes by definition, which we need later
      have upperTriangle : l₂ ≫ h' = a₂ := PushoutCocone.IsColimit.inl_desc pushout a₂ h.l h.fac_left.symm
      use h'
      -- It remains to show that the lower triangle in `sq₂` commutes, for which we need the uniqueness
      -- of maps out of pushouts recorded in `IsColimit.hom_ext`
      · have h₀ : l₂ ≫ b₂ = l₂ ≫ h' ≫ r := by
          rw [← sq₂.w, ← Category.assoc, upperTriangle]
        have h₁ : b₁ ≫ b₂ = b₁ ≫ h' ≫ r := by
          have tr₁ : b₁ ≫ b₂ = h.l ≫ r := by
            simp [h.fac_right]
          have tr₂ : b₁ ≫ h' = h.l := by
            apply PushoutCocone.IsColimit.inr_desc pushout a₂ h.l h.fac_left.symm
          rw [tr₁, ← Category.assoc, tr₂]
        have := PushoutCocone.IsColimit.inr_desc pushout a₂ h.l h.fac_left.symm
        apply (PushoutCocone.IsColimit.hom_ext pushout h₀ h₁).symm

-- (dual : RLP ist stable under pullback)
#check StableUnderBaseChange
