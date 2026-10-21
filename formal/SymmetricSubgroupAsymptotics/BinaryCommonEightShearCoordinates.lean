import SymmetricSubgroupAsymptotics.BinaryBooleanFourDifferenceOperators
import SymmetricSubgroupAsymptotics.BinaryThreeVariablePairMonomialWidth
import SymmetricSubgroupAsymptotics.BinaryPairCanonicalPointCoordinates
import SymmetricSubgroupAsymptotics.BinaryRegular46GraphHeadRigidity
import SymmetricSubgroupAsymptotics.BinaryHeisenberg14GraphHeadRigidity
import SymmetricSubgroupAsymptotics.BinaryElementary16GraphHeadRigidity

/-! The common eight-dimensional shear space on the original points.

The first three original Heisenberg generators are the same regular-eight
translations as in 8T3. Variable zero below is the physical pair bit. The
remaining variables are labelled by these three actual translations. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryCommonEightShearCoordinates

open BinaryElementaryPairMonomialWidth
open BinaryBooleanFourPolynomialCoordinates

/-- Boolean labels to the literal low-eight/high-physical-bit point labels.
This is an explicit relabelling of the same sixteen points. -/
def pointLabels : Equiv.Perm (Fin 16) where
  toFun := ![0,8,7,15,2,10,1,9,4,12,3,11,6,14,5,13]
  invFun := ![0,6,4,10,8,14,12,2,1,7,5,11,9,15,13,3]
  left_inv := by decide
  right_inv := by decide

def originalMonomial (b : Fin 16) : Fin 16 → ZMod 2 :=
  fun x => monomial (support b) (pointLabels.symm x)

/-- Four genuine zero-model permutations: constant pair flip followed by
the three original regular-eight generators. -/
def originalTranslation (i : Fin 4) : Equiv.Perm (Fin 16) :=
  Fin.cases (binaryEightCanonicalPairFrame.affinePermutation 1 (fun _ => 1))
    (fun j => binaryEightCanonicalPairFrame.affinePermutation
      (BinaryMenuCayley8T3.generators j) 0) i

theorem originalTranslation_pointLabels : ∀ (i : Fin 4) (x : Fin 16),
    originalTranslation i (pointLabels x) = pointLabels (flipIndex i x) := by decide +kernel

theorem regular_generators_are_heisenberg : ∀ j : Fin 3,
    BinaryMenuCayley8T3.generators j = BinaryMenuCayley8T22.generators j.castSucc.castSucc := by decide

theorem regular_zero_contains_common_monomials : ∀ b : Fin 16,
    BinaryThreeVariablePairMonomialWidth.Allowed (support b) →
      binaryEightCanonicalLayerChange (originalMonomial b) ∈
        (BinaryRegular46GraphHeadRigidity.stateChart 0).space := by
  simp only [BinaryCoordinateSpace.mem_iff]
  unfold BinaryThreeVariablePairMonomialWidth.Allowed
  decide +kernel

theorem heisenberg_zero_contains_common_monomials : ∀ b : Fin 16,
    BinaryThreeVariablePairMonomialWidth.Allowed (support b) →
      binaryEightCanonicalLayerChange (originalMonomial b) ∈
        (BinaryHeisenberg14GraphHeadRigidity.stateChart 0).space := by
  simp only [BinaryCoordinateSpace.mem_iff]
  unfold BinaryThreeVariablePairMonomialWidth.Allowed
  decide +kernel

theorem elementary_zero_contains_common_monomials : ∀ b : Fin 16,
    BinaryThreeVariablePairMonomialWidth.Allowed (support b) →
      binaryEightCanonicalLayerChange (originalMonomial b) ∈
        (BinaryElementary16GraphHeadRigidity.stateChart 0).space := by
  simp only [BinaryCoordinateSpace.mem_iff]
  unfold BinaryThreeVariablePairMonomialWidth.Allowed
  decide +kernel

end SymmetricSubgroupAsymptotics.BinaryCommonEightShearCoordinates
