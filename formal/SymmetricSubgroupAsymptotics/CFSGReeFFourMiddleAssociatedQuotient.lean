import SymmetricSubgroupAsymptotics.CFSGGradedMatrixAssociatedUnitHom
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleGradedDerivedAction
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! The literal middle-parabolic and derived-parabolic quotients by their
actual graded kernels are faithful associated-graded matrix images. This
does not identify either image with an abstract Levi group or assume that
an associated-graded factor is exceptional-Ree fixed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleAssociatedQuotient
open CFSGGradedMatrixAssociatedDiagonal CFSGGradedMatrixAssociatedUnitHom
open CFSGGradedMatrixTriangularUnits CFSGGradedMatrixSubgroups
open CFSGReeFFourMiddleGradedKernel CFSGReeFFourMiddleGradedDerivedAction
open CFSGReeFFourMiddleParabolicFlag CFSGReeFFourFieldParameters
open CFSGTwistedE6GeckDiagramCovariance
private instance : DecidableEq (CFSGNormTwoRootPairing.Roots CartanMatrix.E₆) := Classical.decEq _
private instance gradedKernelNormal (m : ℕ) : (gradedKernel m).Normal := gradedKernel_normal m

def parabolicToTriangular (m : ℕ) : middleParabolic m →*
    triangularUnits (K := Field m) (fun i => -middleWeight i) :=
  (parabolicRawHom m).codRestrict _ (fun g => by
    change CFSGReeFFourFixedPositiveFamilies.fixedRawHom m g.val ∈ middleFlag (Field m)
    exact middleParabolic_le_flag m g.property)

def middleAssociatedHom (m : ℕ) :
    middleParabolic m →* (Matrix GeckIndex GeckIndex (Field m))ˣ :=
  (associatedUnitHom middleWeight).comp (parabolicToTriangular m)

theorem middleAssociatedHom_val (m : ℕ) (g : middleParabolic m) :
    (middleAssociatedHom m g : Matrix GeckIndex GeckIndex (Field m)) =
      associatedDiagonal middleWeight (parabolicRawHom m g : Matrix GeckIndex GeckIndex (Field m)) := rfl

private theorem associated_comp_ker {I K G : Type*} [Fintype I] [DecidableEq I]
    [_root_.Field K] [Group G] (w : I → ℤ) (rho : G →* (Matrix I I K)ˣ)
    (htri : ∀ g, rho g ∈ triangularUnits (fun i => -w i)) :
    ((associatedUnitHom w).comp (rho.codRestrict _ htri)).ker =
      (strictUnits w).comap rho := by
  ext g
  exact associatedUnitHom_eq_one_iff w ((rho.codRestrict _ htri) g)

theorem middleAssociatedHom_ker (m : ℕ) :
    (middleAssociatedHom m).ker = gradedKernel m :=
  associated_comp_ker middleWeight (parabolicRawHom m)
    (fun g => (parabolicToTriangular m g).property)

theorem middleAssociatedHom_mem_preserving (m : ℕ) (g : middleParabolic m) :
    middleAssociatedHom m g ∈ preservingUnits middleWeight :=
  associatedUnit_mem_preserving middleWeight (parabolicToTriangular m g)

def derivedAssociatedHom (m : ℕ) :
    derivedParabolic m →* (Matrix GeckIndex GeckIndex (Field m))ˣ :=
  (middleAssociatedHom m).comp (toParabolic m)

theorem derivedAssociatedHom_ker (m : ℕ) :
    (derivedAssociatedHom m).ker = derivedGradedKernel m := by
  change (middleAssociatedHom m).ker.comap (toParabolic m) = derivedGradedKernel m
  rw [middleAssociatedHom_ker]
  rfl

def parabolicQuotientEquivImage (m : ℕ) :
    middleParabolic m ⧸ gradedKernel m ≃* (middleAssociatedHom m).range :=
  (QuotientGroup.quotientMulEquivOfEq (middleAssociatedHom_ker m).symm).trans
    (QuotientGroup.quotientKerEquivRange (middleAssociatedHom m))

def derivedQuotientEquivImage (m : ℕ) :
    derivedParabolic m ⧸ derivedGradedKernel m ≃* (derivedAssociatedHom m).range :=
  (QuotientGroup.quotientMulEquivOfEq (derivedAssociatedHom_ker m).symm).trans
    (QuotientGroup.quotientKerEquivRange (derivedAssociatedHom m))

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleAssociatedQuotient
