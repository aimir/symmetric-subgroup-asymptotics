import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignStructural

/-!
# Elementary binary quotients of the four-block comparator

The fixed comparator

`QStarGroup = (S₃ ≀ C₂) × C₂²`

has an elementary binary quotient of rank four.  The first two coordinates
are the abelian quotient of `D₈ = C₂ ≀ C₂`: product of the two base
coordinates and the block swap.  The last two coordinates are the two
displayed auxiliary factors of `QStarGroup`.

Keeping all four quotient maps explicit lets the recursive central-binary
comparison handle an arbitrary order-four projective top uniformly.  No
choice between the cyclic and Klein-four cases is required.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace DegreeThreeFourBlockTwoSignComparator

private abbrev C2 := Multiplicative (ZMod 2)

/-- The product of the two binary base coordinates. -/
def d8BaseProduct : C2 × C2 →* C2 where
  toFun x := x.1 * x.2
  map_one' := by simp
  map_mul' x y := by
    change (x.1 * y.1) * (x.2 * y.2) =
      (x.1 * x.2) * (y.1 * y.2)
    ac_rfl

/-- The abelian rank-two quotient of the literal dihedral target. -/
def d8BinaryPlane : DegreeSixS3Wreath.D8 →* (C2 × C2) where
  toFun x := (x.left.1 * x.left.2, x.right)
  map_one' := by simp
  map_mul' x y := by
    apply Prod.ext
    · rw [C2Wreath.mul_left']
      rcases C2Wreath.cases x.right with hx | hx
      · rw [hx, C2Wreath.swapAut_one]
        change (x.left.1 * y.left.1) * (x.left.2 * y.left.2) =
          (x.left.1 * x.left.2) * (y.left.1 * y.left.2)
        ac_rfl
      · rw [hx, C2Wreath.swapAut_gen]
        change (x.left.1 * y.left.2) * (x.left.2 * y.left.1) =
          (x.left.1 * x.left.2) * (y.left.1 * y.left.2)
        ac_rfl
    · rfl

theorem d8BinaryPlane_surjective : Function.Surjective d8BinaryPlane := by
  rintro ⟨a, b⟩
  refine ⟨⟨(a, 1), b⟩, ?_⟩
  exact Prod.ext (by simp [d8BinaryPlane]) rfl

/-- Nested left-associated elementary binary targets. -/
abbrev Binary1 := C2
abbrev Binary2 := C2 × C2
abbrev Binary3 := (C2 × C2) × C2
abbrev Binary4 := ((C2 × C2) × C2) × C2

/-- All four independent binary coordinates of `QStar`. -/
def qStarToBinary4 : QStarGroup →* Binary4 :=
  ((d8BinaryPlane.prodMap (MonoidHom.id C2)).prodMap
    (MonoidHom.id C2)).comp qStarToD8C2C2

theorem qStarToBinary4_surjective :
    Function.Surjective qStarToBinary4 :=
  ((d8BinaryPlane_surjective.prodMap Function.surjective_id).prodMap
    Function.surjective_id).comp qStarToD8C2C2_surjective

/-- Forget the fourth elementary binary coordinate. -/
def qStarToBinary3 : QStarGroup →* Binary3 :=
  (MonoidHom.fst Binary3 C2).comp qStarToBinary4

theorem qStarToBinary3_surjective :
    Function.Surjective qStarToBinary3 :=
  Prod.fst_surjective.comp qStarToBinary4_surjective

/-- Forget the third and fourth elementary binary coordinates. -/
def qStarToBinary2 : QStarGroup →* Binary2 :=
  (MonoidHom.fst Binary2 C2).comp qStarToBinary3

theorem qStarToBinary2_surjective :
    Function.Surjective qStarToBinary2 :=
  Prod.fst_surjective.comp qStarToBinary3_surjective

/-- Retain one elementary binary coordinate. -/
def qStarToBinary1 : QStarGroup →* Binary1 :=
  (MonoidHom.fst C2 C2).comp qStarToBinary2

theorem qStarToBinary1_surjective :
    Function.Surjective qStarToBinary1 :=
  Prod.fst_surjective.comp qStarToBinary2_surjective

end DegreeThreeFourBlockTwoSignComparator
end SymmetricSubgroupAsymptotics

end
