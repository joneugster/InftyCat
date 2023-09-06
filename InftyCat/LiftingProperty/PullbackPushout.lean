import InftyCat.LiftingProperty.Basic

-- TODO: Stability of pullbacks and pushouts

namespace CategoryTheory

namespace MorphismProperty

-- LLP is stable under pushout
#check StableUnderCobaseChange

variable {C : Type*} [Category C] (I : MorphismProperty C)

theorem solveMe : StableUnderCobaseChange (leftLiftingProperty I) := sorry

-- (dual : RLP ist stable under pullback)
#check StableUnderBaseChange
