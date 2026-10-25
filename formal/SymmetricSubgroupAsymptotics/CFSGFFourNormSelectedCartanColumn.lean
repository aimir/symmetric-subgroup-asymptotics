import SymmetricSubgroupAsymptotics.CFSGFFourE6NormMatrixAction

/-! A single actual norm26 column tests the sparse selected-word model:
short node one moves the first Cartan orbit into the simple-root orbit
represented by node four. No matrix or word certificate is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourNormSelectedCartanColumn
open CFSGFFourE6NormPairRepresentatives CFSGFFourE6NormQuotientCoefficientPilot
open CFSGFFourE6NormQuotientOuterCoefficientPilot CFSGFFourE6NormSimpleParameters
open CFSGFFourE6NormMatrixAction CFSGFFourE6CharacteristicTwoNormImage
open CFSGFFourE6CharacteristicTwoNormBasis CFSGFFourE6NormQuotientSelectedCoefficients
open CFSGFFourE6NormQuotientCoordinateRootActions CFSGFFourSerreMatrices
open CFSGFFourE6NormSimpleCoefficientPilot
open CFSGSerreQuadraticMatrix
local instance : Fintype PairIndex := by unfold PairIndex; infer_instance
local instance : DecidableEq PairIndex := by unfold PairIndex; infer_instance

private def rootFour : rootRepresentatives :=
  ⟨Pi.single (4 : Fin 6) (1 : ℤ),by decide +kernel⟩

def rootFourIndex : PairIndex := Sum.inr rootFour

theorem first_coefficient : ∀j : PairIndex,
    normCoefficient (firstEntry 1) j (Sum.inl 0) =
      if j = rootFourIndex then 1 else 0 := by
  intro j
  cases j with
  | inl i => fin_cases i <;> decide +kernel
  | inr r =>
    have hnot : r.val ≠ simpleVector 2 := by
      intro he
      have hr := r.property
      rw [he] at hr
      exact (by decide +kernel : simpleVector 2 ∉ rootRepresentatives) hr
    have he : (Sum.inr r : PairIndex) = rootFourIndex ↔ r.val = simpleVector 4 := by
      change Sum.inr r = Sum.inr rootFour ↔ _
      rw [Sum.inr.injEq,Subtype.ext_iff]
      rfl
    calc
      normCoefficient (firstEntry 1) (Sum.inr r) (Sum.inl 0) =
          if r.val = simpleVector 4 then 1 else 0 := by
        simp only [normCoefficient,firstEntry,normIndex,partnerIndex,
          cartanRepresentative,CFSG.Models.e6Twist]
        simp [shortFirst,stepEntry,CartanMatrix.E₆,hnot]
      _ = _ := if_congr he.symm rfl rfl

theorem second_coefficient : ∀j : PairIndex,
    normCoefficient (quadraticEntry 1) j (Sum.inl 0) = 0 := by decide +kernel

theorem actual_short_column (K : Type) [Field K] [CharP K 2] (t : K) (j : PairIndex) :
    normCoordinateEquiv K
      (normAction K (foldedRoot K false 1 t) (normBasis K (Sum.inl 0))) j =
        (Pi.single (Sum.inl 0) (1 : K) : PairIndex → K) j +
          t*(Pi.single rootFourIndex (1 : K) : PairIndex → K) j := by
  rw [←normMatrixAction_entry,normMatrixAction_positive_entry,
    first_norm_coefficient,quadratic_norm_coefficient,first_coefficient,second_coefficient]
  simp only [Int.cast_zero,mul_zero,add_zero,Int.cast_ite,Int.cast_one,Pi.single_apply]
  split_ifs <;> rfl

end SymmetricSubgroupAsymptotics.CFSGFFourNormSelectedCartanColumn
