import Mathlib

/-!
This file contains basic API that seems to be missing in mathlib.
-/

namespace CategoryTheory

#check IsPushout

universe u

variable {C : Type u} [Category C]



example {Z X Y P Q : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}
    {a : X ⟶ Q} {b : Y ⟶ Q}
    (p : IsPushout f g inl inr) (sq : CommSq f g a b) :
    ∃ h : P ⟶ Q, inl ≫ h = a ∧ inr ≫ h = b := by
  rcases p with ⟨sq₂, ⟨p, p_prop, p_uniq⟩⟩
  have s : Limits.Cocone (Limits.span f g) := ⟨P, {
    app := fun e => by
      simp?

      done
    naturality := _
  }⟩
  sorry

  -- let c : Limits.Cocone (Limits.span f g) := sorry
  -- have := p.some.desc c
