import SymmetricSubgroupAsymptotics.CFSGE6GenerationFarMixedSimpleLine
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckIntegralWord
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckPrimitiveRootEntry
import SymmetricSubgroupAsymptotics.CFSGIntegralPrimitiveConjugate

/-! The scalar on the actual far mixed coefficient is an integral unit.
Primitivity of the original E3 and F5 and inverse integer conjugation
force sign +1 or -1, before any reduction of characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGE6GenerationFarMixedSign
open CFSGE6GenerationTorusPilot CFSGE6GenerationBranchLattice
open CFSGE6GenerationFarMixedSimpleLine CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGNormTwoRootPairing
open CFSGNormTwoGeckColumns CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord
open CFSGNormTwoGeckIntegralWord CFSGNormTwoGeckPrimitiveRootEntry
local instance : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _

theorem exists_coefficient_sign : ∃ε : ℤ,(ε=1 ∨ ε= -1) ∧
    farCoefficient ℚ=(ε:ℚ) • RootPairing.GeckConstruction.f (E6Index 5) := by
  obtain ⟨c,hc⟩ := rational_far_simple_line
  let u : (Matrix Index Index ℤ)ˣ := canonicalWord e6Data ℤ farMixedWord
  let X : Matrix Index Index ℤ := CFSGGeckIntegralMatrices.E E6Base (E6Index 3)
  let Y : Matrix Index Index ℤ := CFSGGeckIntegralMatrices.F E6Base (E6Index 5)
  have hcast : (Int.castRingHom ℚ).mapMatrix
      ((u : Matrix Index Index ℤ)*X*((u⁻¹ : (Matrix Index Index ℤ)ˣ) : Matrix Index Index ℤ))=
        c • (Int.castRingHom ℚ).mapMatrix Y := by
    dsimp only [u,X,Y]
    rw [map_mul,map_mul,cast_integer_word,cast_integer_word_inverse,
      CFSGGeckIntegralMatrices.map_E,CFSGGeckIntegralMatrices.map_F]
    simpa only [farCoefficient,CFSGNormTwoGeckRationalAdjointStrings.rational_E_eq] using hc
  have hs := CFSGIntegralPrimitiveConjugate.scalar_eq_sign u X Y
    (Sum.inl (E6Index 3)) (Sum.inr (negativeIndex CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite (E6Index 3)))
    (Sum.inl (E6Index 5)) (Sum.inr (E6Index 5:Roots CartanMatrix.E₆))
    (integer_E_unit_entry CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base (E6Index 3))
    (integer_F_unit_entry CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base (E6Index 5)) c hcast
  rcases hs with hs|hs
  · refine ⟨1,Or.inl rfl,?_⟩
    simpa only [hs,Int.cast_one] using hc
  · refine ⟨-1,Or.inr rfl,?_⟩
    simpa only [hs,Int.cast_neg,Int.cast_one] using hc

end SymmetricSubgroupAsymptotics.CFSGE6GenerationFarMixedSign
