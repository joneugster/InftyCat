import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Arrow
import Mathlib.CategoryTheory.Limits.Shapes.CommSq
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.LiftingProperties.Basic
import Mathlib.CategoryTheory.LiftingProperties.Adjunction
import Mathlib.CategoryTheory.MorphismProperty
import Mathlib.CategoryTheory.EqToHom

namespace CategoryTheory


variable {𝓒 : Type u} [Category.{v} 𝓒]

/- 
A __morphism class__ is any collection of the morphisms of category 𝓒. 
Here X ⟶ Y is the type `quiver.hom X Y` projected out of the category structure of `𝓒`.  
We use predicate `MorphismProperty ` already in Mathlib. 
-/

variable (I : MorphismProperty 𝓒)

#check eqToHom


@[simp] 
lemma of_eq_left {X' X Y} (f : X ⟶ Y) (e : X' = X) : I (eqToHom e ≫ f) ↔ I f :=
by subst e; simp


@[simp] 
lemma of_eq_right {X Y Y'} (f : X ⟶ Y) (e : Y = Y') : I (f ≫ eqToHom e) ↔ I f :=
by subst e; simp



/-
__lifting property__

       f
    A ---> x
    |     /|
  i |   /  | p
    v /    v
    b ---> y
       g 
-/

#check HasLiftingProperty


/- A __diagonal filler__ is a function that takes a commutative square which has a lifting property and returns a diagonal filler. -/

structure Filler {a b x y : 𝓒} (i : a ⟶ b) (p : x ⟶ y) [HasLiftingProperty i p] (f : a ⟶ x) (g : b ⟶ y) (comm_sq : CommSq f i p g) := 
(map : b ⟶ x)
(eq_up : i ≫ map = f)
(eq_down : map ≫ p  = g)


/-- 
__left lifting property__
A class `llp R` of morphisms consist of morphisms `i` which are left orthogonal to every morphism `p` in `R`.
-/
def LLP (R : MorphismProperty 𝓒) : MorphismProperty 𝓒 :=
fun a b i ↦ ∀ ⦃x y⦄ ⦃p : x ⟶ y⦄, R p → HasLiftingProperty i p


/-- 
__right lifting property__
A class `rlp L` consists of morphisms `p` which are left orthogonal to every morphism `i` in `L` (morphisms with left lifting property wrt R)
-/
def RLP (L : MorphismProperty 𝓒) : MorphismProperty 𝓒 :=
fun x y p ↦ ∀ ⦃a b⦄ ⦃i : a ⟶ b⦄, L i → HasLiftingProperty i p


structure LLP_RLP (L R : MorphismProperty 𝓒) : Prop :=
(llp : L = LLP R)
(rlp : R = RLP L)

structure isWFS (L R : MorphismProperty 𝓒) extends LLP_RLP L R  : Prop :=
(fact : ∀ {x y} (f : x ⟶ y), ∃ (z : 𝓒) (i : x ⟶ z) (p : z ⟶ y), L i ∧ R p ∧ i ≫ p = f)


namespace CommSq 
variables {a b a' b' a'' b'' : 𝓒} {f : a ⟶ b} {g : a' ⟶ b'} {h : a'' ⟶ b''} {u : a ⟶ a'} {u' : a' ⟶ a'' } {v : b ⟶ b'} {v' : b' ⟶ b''}

-- `comm_sq top left right bottom`
def HorPaste  (s : CommSq u f g v) (s' : CommSq u' g h v') : CommSq (u ≫ u') f h (v ≫ v') where  
  w := by 
            rw [Category.assoc] 
            rw [s'.w]
            rw [← Category.assoc] 
            rw [s.w] 
            rw [Category.assoc]

end CommSq



/-- A morphism `g` is a retract of morphism `f` if `g`, considered as an object in the arrow category is a retract of `f`. 
 ``` 
  c ---ia---> a ---ra---> c 
  |           |           |
  g           f           g
  |           |           |
  v           v           v 
  d ---ib---> b ---rb---> d

```
-/  
structure Retract {a b c d : 𝓒} (f : a ⟶ b) (g : c ⟶ d) : Type v := 
(ia : c ⟶ a) (ra : a ⟶ c)
(ib : d ⟶ b) (rb : b ⟶ d)
(hi : CommSq ia g f ib)
(hr : CommSq ra f g rb)
(ha : ia ≫ ra = 𝟙 c)
(hb : ib ≫ rb = 𝟙 d)




/-
The left class of a WFS is closed under retracts. 
(* proposition 14.1.13 in More Concise AT *)
-/

lemma is_wfs.retract {L R : MorphismProperty 𝓒} (w : isWFS L R)
  {a b c d} {f : a ⟶ b} {g : c ⟶ d} (ρ : Retract f g) (hf : L f) : L g :=
by 
  rw [w.llp] -- to prove Lg we prove g ⋔ p for all p with Rp  
  --unfold llp, 
  intro x y p hrp 
  refine {sq_hasLift := _}
  intro u v hcomm
  have hcomm' : comm_sq (ρ.ra ≫ u) f p (ρ.rb ≫ v) :=  CommSq.hor_paste ρ.hr hcomm -- pasting commutative square of retract with the comm square of the lift problem 
  -- refine {exists_lift := _}, 
  have hd : hcomm'.hasLift := by apply (w.lp hf hrp).sq_hasLift hcomm' -- lift the pasted comm square
  repeat{cases hd} 
  refine {exists_lift := _}
  let retract_lift := ρ.ib ≫ hd_l  -- the lift of the pasted comm square is the retract of the lift of the original comm square  
  use retract_lift
  · simp [← category.assoc, ← ρ.hi.w, category.assoc, hd_fac_left', ← category.assoc, ρ.ha]
  · simp [category.assoc, hd_fac_right', ← category.assoc, ρ.hb ]
  



lemma is_wfs.retract_alt {L R : MorphismProperty 𝓒} (w : isWFS L R)
  {a b c d} {f : a ⟶ b} {g : c ⟶ d} (ρ : Retract f g) (hf : L f) : L g :=
by 
  rw [w.llp] -- to prove Lg we prove g ⋔ p for all p with Rp  
  --unfold llp, 
  intro x y p hrp 
  refine' {sq_hasLift := _}
  intro u v hcomm
  -- have hcomm' : comm_sq (ρ.ra ≫ u) f p (ρ.rb ≫ v) :=  CommSq.hor_paste ρ.hr hcomm -- pasting commutative square of retract with the comm square of the lift problem 






end CategoryTheory




