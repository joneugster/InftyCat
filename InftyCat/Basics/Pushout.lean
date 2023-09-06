import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.CategoryTheory.Limits.Filtered

import Mathlib.Init.Algebra.Order
import Mathlib.CategoryTheory.Limits.Shapes.CommSq

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


variable {Q : C} {a : X ⟶ Q} {b : Y ⟶ Q} (sq : CommSq f g a b)

/-- This is the map coming from the universal property of the pushout. -/
noncomputable
def IsPushout.mapOfCommSq : P ⟶ Q :=
  (Classical.choice (p.isColimit')).desc sq.cocone

/-- The proof that `inl ≫ IsPushout.mapOfCommSq p sq = a`. -/
noncomputable
def IsPushout.mapOfCommSq_commutes₁ : inl ≫ IsPushout.mapOfCommSq p sq = a :=
  (Classical.choice (p.isColimit')).fac sq.cocone .left

/-- The proof that `inr ≫ IsPushout.mapOfCommSq p sq = b`. -/
noncomputable
def IsPushout.mapOfCommSq_commutes₂ :  inr ≫ IsPushout.mapOfCommSq p sq = b :=
  (Classical.choice (p.isColimit')).fac sq.cocone .right

#check p.mapOfCommSq_commutes₁ sq

noncomputable
def IsPushout.mapOfCommSqUniq := (Classical.choice (p.isColimit')).uniq sq.cocone


example {Q : C} {a : X ⟶ Q} {b : Y ⟶ Q} (sq : CommSq f g a b) :
    ∃ h : P ⟶ Q, inl ≫ h = a ∧ inr ≫ h = b := by
  use p.mapOfCommSq sq
  -- rcases p with ⟨sq₂, ⟨p, p_fac, _⟩⟩
  -- let h := p sq.cocone
  -- change P ⟶ Q at h
  -- let h_fac := p_fac sq.cocone
  -- use h
  constructor
  · exact p.mapOfCommSq_commutes₁ sq
  · exact p.mapOfCommSq_commutes₂ sq