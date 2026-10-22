import SymmetricSubgroupAsymptotics.CFSGSerreRootDirection
import SymmetricSubgroupAsymptotics.CFSGSerreGeneratorRelations
import SymmetricSubgroupAsymptotics.CFSGSerreModelRootGeneration

/-! Commutation at distinct orthogonal nodes in the ORIGINAL Serre
construction. Rational defining relations imply commuting adjoints;
divided powers are restricted to the SAME integral lattice before base
change. No natural-image injectivity or classical-group identification
is used. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators TensorProduct

namespace SymmetricSubgroupAsymptotics.CFSGSerreCrossNodeCommutation
open CFSG.Models.Chevalley CFSGSerreLocalNilpotence CFSGSerreDividedPowers
variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)

theorem rootVector_lie_zero_of_cartan_zero (neg : Bool) (i j : Fin n)
    (hij : A i j = 0) : ⁅rootVector A neg i, rootVector A neg j⁆ = 0 := by
  cases neg
  · have h := generator_adE A i j
    simpa only [hij, neg_zero, Int.toNat_zero, zero_add, pow_one,
      LieAlgebra.ad_apply, rootVector, Bool.false_eq_true, if_false] using h
  · have h := generator_adF A i j
    simpa only [hij, neg_zero, Int.toNat_zero, zero_add, pow_one,
      LieAlgebra.ad_apply, rootVector, if_true] using h

theorem dividedPowers_commute_of_lie_zero (e f : Bool) (i j : Fin n)
    (hij : ⁅rootVector A e i, rootVector A f j⁆ = 0) (k l : ℕ) :
    Commute (dividedPower A e i k) (dividedPower A f j l) := by
  have had : Commute
      (LieAlgebra.ad ℚ (RationalLie A) (rootVector A e i))
      (LieAlgebra.ad ℚ (RationalLie A) (rootVector A f j)) := by
    have h := congrArg (LieAlgebra.ad ℚ (RationalLie A)) hij
    rw [LieHom.map_lie, map_zero] at h
    change _ * _ - _ * _ = 0 at h
    exact sub_eq_zero.mp h
  have hp := had.pow_pow k l
  have hc : Commute
      ((k.factorial : ℚ)⁻¹ • (LieAlgebra.ad ℚ (RationalLie A) (rootVector A e i)) ^ k)
      ((l.factorial : ℚ)⁻¹ • (LieAlgebra.ad ℚ (RationalLie A) (rootVector A f j)) ^ l) := by
    change _ * _ = _ * _
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [hp.eq, mul_comm ((k.factorial : ℚ)⁻¹) ((l.factorial : ℚ)⁻¹)]
  change _ * _ = _ * _
  ext x
  have hx := congrArg (fun F : Module.End ℚ (RationalLie A) => F x) hc.eq
  simpa only [dividedPower, Module.End.mul_apply, LinearMap.restrictScalars_apply] using hx

theorem integralOperators_commute_of_lie_zero (e f : Bool) (i j : Fin n)
    (hij : ⁅rootVector A e i, rootVector A f j⁆ = 0) (k l : ℕ) :
    Commute (integralOperator A e i k) (integralOperator A f j l) := by
  change _ * _ = _ * _
  ext x
  change dividedPower A e i k (dividedPower A f j l x.val) =
    dividedPower A f j l (dividedPower A e i k x.val)
  exact congrArg (fun F : Module.End ℤ (RationalLie A) => F x.val)
    (dividedPowers_commute_of_lie_zero A e f i j hij k l).eq

theorem baseChangedOperators_commute_of_lie_zero (K : Type) [Field K]
    (e f : Bool) (i j : Fin n) (hij : ⁅rootVector A e i, rootVector A f j⁆ = 0)
    (k l : ℕ) :
    Commute ((integralOperator A e i k).baseChange K)
      ((integralOperator A f j l).baseChange K) := by
  have h := congrArg (fun F : Module.End ℤ (integralLattice A) =>
      Module.End.baseChangeHom ℤ K (integralLattice A) F)
    (integralOperators_commute_of_lie_zero A e f i j hij k l).eq
  simpa only [map_mul] using h

theorem rootOperators_commute_of_lie_zero (K : Type) [Field K]
    (e f : Bool) (i j : Fin n) (hij : ⁅rootVector A e i, rootVector A f j⁆ = 0)
    (a b : K) : Commute (rootOperator A K e i a) (rootOperator A K f j b) := by
  unfold rootOperator
  apply Commute.sum_left
  intro k hk
  apply Commute.sum_right
  intro l hl
  show (a ^ k • (integralOperator A e i k).baseChange K) *
      (b ^ l • (integralOperator A f j l).baseChange K) =
    (b ^ l • (integralOperator A f j l).baseChange K) *
      (a ^ k • (integralOperator A e i k).baseChange K)
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [(baseChangedOperators_commute_of_lie_zero A K e f i j hij k l).eq,
    mul_comm (a ^ k) (b ^ l)]

theorem modelRoots_commute_of_lie_zero (K : Type) [Field K]
    (e f : Bool) (i j : Fin n) (hij : ⁅rootVector A e i, rootVector A f j⁆ = 0)
    (a b : K) :
    Commute (CFSGSerreModelRootGeneration.modelRoot A K e i a)
      (CFSGSerreModelRootGeneration.modelRoot A K f j b) := by
  change _ * _ = _ * _
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  change rootOperator A K e i a * rootOperator A K f j b =
    rootOperator A K f j b * rootOperator A K e i a
  exact (rootOperators_commute_of_lie_zero A K e f i j hij a b).eq

theorem modelRoots_commute_of_cartan_zero (K : Type) [Field K]
    (neg : Bool) (i j : Fin n) (hij : A i j = 0) (a b : K) :
    Commute (CFSGSerreModelRootGeneration.modelRoot A K neg i a)
      (CFSGSerreModelRootGeneration.modelRoot A K neg j b) :=
  modelRoots_commute_of_lie_zero A K neg neg i j
    (rootVector_lie_zero_of_cartan_zero A neg i j hij) a b

end SymmetricSubgroupAsymptotics.CFSGSerreCrossNodeCommutation
