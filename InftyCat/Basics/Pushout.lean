import Mathlib

/-!
This file contains basic API that seems to be missing in mathlib.
-/

namespace CategoryTheory

#check IsPushout

#check Functor

universe u

variable {C : Type u} [Category C]

variable {Z X Y P Q : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}
variable (p : IsPushout f g inl inr)

-- def IsPushout.cocone : Limits.Cocone (Limits.span f g) := sorry

example {Q : C} {a : X ⟶ Q} {b : Y ⟶ Q} (sq : CommSq f g a b) :
    ∃ h : P ⟶ Q, inl ≫ h = a ∧ inr ≫ h = b := by
  rcases p with ⟨sq₂, ⟨p, p_fac, _⟩⟩
  let h := p sq.cocone
  change P ⟶ Q at h
  let h_fac := p_fac sq.cocone
  use h
  constructor
  · exact h_fac .left
  · exact h_fac .right