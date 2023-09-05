import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.CategoryTheory.Limits.Filtered

open CategoryTheory

universe u

variable {C : Type u} [Category C]

-- Not sure about this name
def StronglyDirected {α : Type u} {ι : Sort w}
  (r : α → α → Prop) (f : ι → α) (κ : Cardinal) :=
  ∀ σ, Cardinal.mk σ < κ → (∀ g : σ → ι, ∃ m, ∀ x, r (f (g x)) m)


/- class IsCompact {x y: C} (f : x ⟶ y) (κ : Cardinal)
  [Limits.HasFilteredColimitsOfSize C]
  : Prop where
  cat_hasFilteredColims : f = f
-/

