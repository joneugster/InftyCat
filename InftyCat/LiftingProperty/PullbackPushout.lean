import InftyCat.LiftingProperty.Basic
import InftyCat.Basics.Pushout
import ProofWidgets.Component.GoalTypePanel

-- TODO: Stability of pullbacks

namespace CategoryTheory

open Limits

namespace MorphismProperty

-- LLP is stable under pushout
#check StableUnderCobaseChange

variable {C : Type*} [Category C] (L R : MorphismProperty C)

  structure PushoutWithDesc {Z X Y P T : C} (f : Z ⟶ X) (g : Z ⟶ Y) (inl : X ⟶ P) (inr : Y ⟶ P)
      (a : X ⟶ T) (b: Y ⟶ T) extends IsPushout f g inl inr where
    desc : P ⟶ T 
    outerSquare : CommSq f g a b
    inlComm : inl ≫ desc = a
    inrComm : inr ≫ desc = b 

  noncomputable def PushoutWithDescFromSq {Z X Y P T : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}
      {a : X ⟶ T} {b: Y ⟶ T} (hp : IsPushout f g inl inr) (hsq : CommSq f g a b) : 
      PushoutWithDesc f g inl inr a b := {
    w := hp.toCommSq.w
    isColimit' := hp.isColimit'    
    desc := PushoutCocone.IsColimit.desc hp.isColimit'.some a b hsq.w
    inlComm := PushoutCocone.IsColimit.inl_desc hp.isColimit'.some a b hsq.w
    inrComm := PushoutCocone.IsColimit.inr_desc hp.isColimit'.some a b hsq.w
    outerSquare := hsq}

  namespace CommSq

  lemma horizontalPaste {A₁ A₂ A₃ B₁ B₂ B₃ : C} {a₁ : A₁ ⟶ A₂} {a₂ : A₂ ⟶ A₃} {b₁ : B₁ ⟶ B₂} {b₂ : B₂ ⟶ B₃}
      {f₁: A₁ ⟶ B₁} {f₂: A₂ ⟶ B₂} {f₃: A₃ ⟶ B₃} (leftSq : CommSq a₁ f₁ f₂ b₁) (rightSq : CommSq a₂ f₂ f₃ b₂) : 
      CommSq (a₁ ≫ a₂) f₁ f₃ (b₁ ≫ b₂) := by 
    constructor
    rw [Category.assoc, rightSq.w, ← Category.assoc, leftSq.w, ← Category.assoc]
  
  end CommSq

  theorem llpStableUnderCobaseChange : StableUnderCobaseChange (leftLiftingProperty R) := by
    -- Unpack the definition of being stable under cobase change (pushout) and introduce an arbitrary pushout
    simp [StableUnderCobaseChange]
    intro A B A' B' l₁ a₁ l₂ b₁ hB' hl₁
    let sq₁ := hB'.toCommSq
    -- Unpack the definition of the left lifting property and introduce an arbitrary lifting diagram
    simp [leftLiftingProperty]
    intro A'' B'' r hr
    -- Note that since `l₁` has the left lifting property against `R` and `r` is in `R`, 
    -- it has lifts against `r`
    specialize hl₁ r hr
    constructor
    intro a₂ b₂ sq₂
    -- Construct the outer commutative square, which has a lift by assumption
    have sq₃ := CommSq.horizontalPaste sq₁ sq₂
    have hsq₃ := HasLiftingProperty.sq_hasLift sq₃
    let h := hsq₃.exists_lift.some
    -- To show that `sq₂` has a lift, we call `constructor` on it to reduce to the
    -- statement that its `LiftStruct` is nonempty
    constructor
    let sq₄ : CommSq a₁ l₁ a₂ h.l := {
      w := h.fac_left.symm
    }
    -- Construct a `PushoutWithDesc`, consisting of a pushout square and a descending map from the 
    -- bottom right object `B'` to `A''` (the desired lift `h'`) together with the two obvious
    -- commutative triangles, and use `h'` as candidate for the `LiftStruct`
    let pWithDesc := PushoutWithDescFromSq hB' sq₄
    let h' := pWithDesc.desc
    use h'
    · exact pWithDesc.inlComm
    -- It remains to show that the lower triangle in `sq₂` commutes, for which we need the uniqueness
    -- of maps out of pushouts recorded in `IsColimit.hom_ext`
    · have h₀ : l₂ ≫ b₂ = l₂ ≫ h' ≫ r := by
        rw [← sq₂.w, ← Category.assoc, pWithDesc.inlComm]
      have h₁ : b₁ ≫ b₂ = b₁ ≫ h' ≫ r := by
        have tr₁ : b₁ ≫ b₂ = h.l ≫ r := by
          simp [h.fac_right]
        have tr₂ : b₁ ≫ h' = h.l := by
          exact pWithDesc.inrComm
        rw [tr₁, ← Category.assoc, tr₂]
      let pushout := hB'.isColimit'.some
      exact (PushoutCocone.IsColimit.hom_ext pushout h₀ h₁).symm

-- (dual : RLP ist stable under pullback)

#check StableUnderBaseChange
