import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveFunctionalIntersection
import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterInversionRoots
import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterGradedQuotient

/-! A positive root of zero inside height is one of the three orthogonal
outer simple roots, hence becomes negative under the actual outer word.
Its full positive remainder therefore belongs to the strict inside-height
kernel. This is uniform lattice support, without a root census. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOuterPositiveRemainderSupport
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoCoordinatePositiveRootGenerators CFSGNormTwoCoordinateOrthogonalRootSupport
open CFSGReeFFourOuterInversionRoots CFSGReeFFourOuterParabolicFlag
open CFSGReeFFourOuterGradedQuotient CFSGNormTwoCoordinatePositiveFunctionalIntersection
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckLatticeDegree
open CFSGGradedMatrixSubgroups CFSGNormTwoGeckHeightSupport
open CFSGNormTwoGeckPositivePGroup
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
private instance : DecidableEq (Roots A) := Classical.decEq _

private theorem nodes_orthogonal :
    ∀ i ∈ blockNodes, ∀ j ∈ blockNodes, i ≠ j → A j i = 0 := by
  decide +kernel

theorem insideHeight_nonnegative (a : PositiveRoot A) : 0 ≤ insideHeight a.val.val := by
  change 0 ≤ (a.val.val 2 + a.val.val 3) + a.val.val 4
  exact add_nonneg (add_nonneg (a.property 2) (a.property 3)) (a.property 4)

theorem outer_zero_goes_negative (a : PositiveRoot A) (ha : insideHeight a.val.val = 0) :
    ¬ ∀ j, 0 ≤ (wordRoot A hs hp b₀ s₀ blockWord a.val).val j := by
  have hz : (a.val.val 2 + a.val.val 3) + a.val.val 4 = 0 := ha
  have hsupport : ∀ i, i ∉ ({i | i ∈ blockNodes} : Set (Fin 6)) → a.val.val i = 0 := by
    intro i hi
    have hp2 := a.property 2
    have hp3 := a.property 3
    have hp4 := a.property 4
    have hcases : i = (2 : Fin 6) ∨ i = (3 : Fin 6) ∨ i = (4 : Fin 6) := by
      simp only [Set.mem_setOf_eq, blockNodes, Finset.mem_insert, Finset.mem_singleton] at hi
      omega
    rcases hcases with rfl | rfl | rfl <;> omega
  obtain ⟨i, hi, he⟩ := positive_root_supported_on_orthogonal_simples A hd hs hp
    {i | i ∈ blockNodes} nodes_orthogonal a.val a.property hsupport
  exact (outer_negative_iff a).mpr ⟨i, hi, he⟩

theorem outer_positive_inside_one (a : PositiveRoot A)
    (ha : ∀ j, 0 ≤ (wordRoot A hs hp b₀ s₀ blockWord a.val).val j) :
    1 ≤ insideHeight a.val.val := by
  have hn := insideHeight_nonnegative a
  have hne : insideHeight a.val.val ≠ 0 := fun h => outer_zero_goes_negative a h ha
  omega

private theorem outerWeight_eq :
    outerWeight = fun j => insideHeight (latticeWeight A hs hp b₀ j) := by
  funext j
  cases j with
  | inl i => exact (map_zero insideHeight).symm
  | inr a => rfl

theorem outer_positive_remainder_le_strict (K : Type) [Field K] [Finite K] :
    rootGroup A hs hp b₀ s₀ K false ⊓
      (rootGroup A hs hp b₀ s₀ K false).comap
        (MulAut.conj (CFSGSerreQuadraticWeylWord.canonicalWord
          (CFSGNormTwoGeckIntegralRealization.realizationData A hs hp b₀ s₀) K blockWord)).toMonoidHom ≤
      strictUnits outerWeight := by
  rw [outerWeight_eq]
  exact positive_intersection_le_strict A hd hs hp ho K blockWord insideHeight
    outer_positive_inside_one

end SymmetricSubgroupAsymptotics.CFSGReeFFourOuterPositiveRemainderSupport
