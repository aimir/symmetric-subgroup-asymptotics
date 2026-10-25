import SymmetricSubgroupAsymptotics.CFSGGradedMatrixAssociatedUnitHom
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixStrictNormal
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixStrictPGroup
import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterParabolicFlag

/-! The actual outer parabolic has a literal normal graded two-kernel.
Its associated image is defined by the same matrix homomorphism, with
an exact kernel equality. No Levi or rank-one recognition is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOuterGradedQuotient
open CFSGGradedMatrixAssociatedDiagonal CFSGGradedMatrixAssociatedUnitHom
open CFSGGradedMatrixSubgroups CFSGGradedMatrixTriangularUnits
open CFSGGradedMatrixStrictNormal CFSGGradedMatrixStrictPGroup
open CFSGReeFFourOuterParabolicFlag CFSGReeFFourFieldParameters
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourFixedModelEquivalence
open CFSGTwistedE6GeckDiagramCovariance CFSGNormTwoGeckHeightSupport
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGFFourOriginalMiddleWords
local notation "A" => CartanMatrix.E₆
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
private instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def outerWeight : GeckIndex → ℤ := weight A hs hp E6Base insideHeight

def parabolicRawHom (m : ℕ) : outerParabolic m →* (Matrix GeckIndex GeckIndex (Field m))ˣ :=
  (fixedRawHom m).comp (outerParabolic m).subtype

theorem parabolicRawHom_injective (m : ℕ) : Function.Injective (parabolicRawHom m) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact rawHom_injective (Field m) h

def gradedKernel (m : ℕ) : Subgroup (outerParabolic m) :=
  (strictUnits (K := Field m) outerWeight).comap (parabolicRawHom m)

theorem gradedKernel_normal (m : ℕ) : (gradedKernel m).Normal := by
  apply comap_strict_normal
  intro g
  change fixedRawHom m g.val ∈ outerFlag (Field m)
  exact outerParabolic_le_flag m g.property

theorem gradedKernel_isPGroup (m : ℕ) : IsPGroup 2 (gradedKernel m) :=
  (strictUnits_isPGroup outerWeight 2).comap_of_injective (parabolicRawHom m)
    (parabolicRawHom_injective m)

def parabolicToTriangular (m : ℕ) : outerParabolic m →*
    triangularUnits (K := Field m) (fun i => -outerWeight i) :=
  (parabolicRawHom m).codRestrict _ (fun g => by
    change fixedRawHom m g.val ∈ outerFlag (Field m)
    exact outerParabolic_le_flag m g.property)

def outerAssociatedHom (m : ℕ) :
    outerParabolic m →* (Matrix GeckIndex GeckIndex (Field m))ˣ :=
  (associatedUnitHom outerWeight).comp (parabolicToTriangular m)

theorem outerAssociatedHom_val (m : ℕ) (g : outerParabolic m) :
    (outerAssociatedHom m g : Matrix GeckIndex GeckIndex (Field m)) =
      associatedDiagonal outerWeight (parabolicRawHom m g : Matrix GeckIndex GeckIndex (Field m)) := rfl

private theorem associated_comp_ker {I K G : Type*} [Fintype I] [DecidableEq I]
    [_root_.Field K] [Group G] (w : I → ℤ) (rho : G →* (Matrix I I K)ˣ)
    (htri : ∀ g, rho g ∈ triangularUnits (fun i => -w i)) :
    ((associatedUnitHom w).comp (rho.codRestrict _ htri)).ker =
      (strictUnits w).comap rho := by
  ext g
  exact associatedUnitHom_eq_one_iff w ((rho.codRestrict _ htri) g)

theorem outerAssociatedHom_ker (m : ℕ) : (outerAssociatedHom m).ker = gradedKernel m :=
  associated_comp_ker outerWeight (parabolicRawHom m)
    (fun g => (parabolicToTriangular m g).property)

theorem outerAssociatedHom_mem_preserving (m : ℕ) (g : outerParabolic m) :
    outerAssociatedHom m g ∈ preservingUnits outerWeight :=
  associatedUnit_mem_preserving outerWeight (parabolicToTriangular m g)

end SymmetricSubgroupAsymptotics.CFSGReeFFourOuterGradedQuotient
