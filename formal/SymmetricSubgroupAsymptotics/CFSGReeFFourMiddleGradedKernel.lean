import SymmetricSubgroupAsymptotics.CFSGGradedMatrixStrictNormal
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleParabolicFlag
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleDerivedFiveRootWords

/-! A literal normal graded kernel in the actual middle parabolic. The
outer root parameters lie in it and the certified positive commutator
is an actual member. No recognition as a maximal radical, cardinality,
proper-index, or outer-automorphism assertion is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleGradedKernel
open CFSGReeFFourMiddleParabolicFlag CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFieldParameters CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourMiddleDerivedFiveRootWords CFSGReeFFourMiddleDerivedFiveWord
open CFSGReeFFourOuterFixedRoot CFSGReeFFourMiddleFixedSubgroup
open CFSGReeFFourMiddleFixedWords CFSGReeFFourRelativePositiveSubgroups
open CFSGReeFFourFixedBruhatCover
open CFSGFFourOriginalMiddleWords CFSGFFourE6FixedGeneratedGroup
open CFSGTwistedE6GeckDiagramCovariance CFSGE6GeckMiddleRootSupport
open CFSGNormTwoGeckArbitraryHeightSupport CFSGNormTwoGeckHeightSupport
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGSerreQuadraticMatrix CFSGGradedMatrixSubgroups
open CFSGGradedMatrixTriangularUnits CFSGGradedMatrixStrictNormal
local notation "A" => CartanMatrix.E₆
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
private instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _

def middleWeight : GeckIndex → ℤ := weight A hs hp E6Base outsideHeight

def parabolicRawHom (m : ℕ) : middleParabolic m →* (Matrix GeckIndex GeckIndex (Field m))ˣ :=
  (fixedRawHom m).comp (middleParabolic m).subtype

def gradedKernel (m : ℕ) : Subgroup (middleParabolic m) :=
  (strictUnits (K := Field m) middleWeight).comap (parabolicRawHom m)

theorem gradedKernel_normal (m : ℕ) : (gradedKernel m).Normal := by
  apply comap_strict_normal
  intro g
  change fixedRawHom m g.val ∈ middleFlag (Field m)
  exact middleParabolic_le_flag m g.property

theorem positive_le_parabolic (m : ℕ) : fixedPositive m ≤ middleParabolic m := by
  change fixedPositive m ≤ (fixedPositive m ⊔ fixedDiagonal m) ⊔
    Subgroup.closure {middleFixedWeyl m}
  exact le_sup_left.trans le_sup_left

def outerParameter (m : ℕ) (a : Field m) : middleParabolic m :=
  ⟨fixedOuterHom m (Multiplicative.ofAdd a), positive_le_parabolic m
    (fixedOuterHom_range_le_fixedPositive m ⟨Multiplicative.ofAdd a,rfl⟩)⟩

theorem outer_raw_strict (m : ℕ) (a : Field m) :
    rawHom (Field m) (outerWord m a) ∈ strictUnits (K := Field m) middleWeight := by
  simp only [outerWord, map_mul, rawHom_root, folded_root_eq_orbitParameter]
  change (canonicalRoot rawData (Field m) false 0 a *
      canonicalRoot rawData (Field m) false 5 a) *
    canonicalRoot rawData (Field m) false 1 (alpha m a) ∈ _
  apply (strictUnits middleWeight).mul_mem
  · apply (strictUnits middleWeight).mul_mem
    · exact canonicalRoot_strict A hs hp E6Base E6Index outsideHeight (Field m) 0 a
        (by change (0 : ℤ) < 1; decide)
    · exact canonicalRoot_strict A hs hp E6Base E6Index outsideHeight (Field m) 5 a
        (by change (0 : ℤ) < 1; decide)
  · exact canonicalRoot_strict A hs hp E6Base E6Index outsideHeight (Field m) 1 (alpha m a)
      (by change (0 : ℤ) < 1; decide)

theorem outerParameter_mem_gradedKernel (m : ℕ) (a : Field m) :
    outerParameter m a ∈ gradedKernel m := outer_raw_strict m a

def fourCycleInParabolic (m : ℕ) : middleParabolic m :=
  ⟨fourCycle m, positive_le_parabolic m
    (middleFixedSubgroup_le_fixedPositive m
      ⟨1,alpha m 1,0,alpha m 0+1^2*alpha m 1,rfl⟩)⟩

def fiveWordInParabolic (m : ℕ) : middleParabolic m := by
  refine ⟨fiveWord m, (middleParabolic m).mul_mem ?_
    ((middleParabolic m).pow_mem (fourCycleInParabolic m).property 2)⟩
  exact (show Subgroup.closure {middleFixedWeyl m} ≤ middleParabolic m from le_sup_right)
    (Subgroup.subset_closure (Set.mem_singleton_iff.mpr rfl))

def commutatorInParabolic (m : ℕ) : middleParabolic m :=
  ⟨positiveCommutator m, positive_le_parabolic m (positiveCommutator_mem_positive m)⟩

theorem commutator_mem_gradedKernel (m : ℕ) :
    commutatorInParabolic m ∈ gradedKernel m := by
  have hx := outerParameter_mem_gradedKernel m 1
  have hc := (gradedKernel_normal m).conj_mem (outerParameter m 1)⁻¹
    ((gradedKernel m).inv_mem hx) (fourCycleInParabolic m)
  have hm := (gradedKernel m).mul_mem hx hc
  change outerParameter m 1 * fourCycleInParabolic m * (outerParameter m 1)⁻¹ *
    (fourCycleInParabolic m)⁻¹ ∈ gradedKernel m
  simpa only [mul_assoc] using hm

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleGradedKernel
