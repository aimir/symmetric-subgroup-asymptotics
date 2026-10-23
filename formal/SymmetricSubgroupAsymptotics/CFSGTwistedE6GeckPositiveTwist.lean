import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckMatrixTwist
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositivePGroup

/-! The literal E6 upper root group and its opposite are preserved by
the actual diagram--field twist. Their p-group property is inherited
from the checked integral-height construction, without fixed-source
surjectivity or a root census. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckPositiveTwist
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckMatrixTwist
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite CFSGSerreDiagram
open CFSGNormTwoGeckPositivePGroup CFSGSerreQuadraticMatrix

abbrev SignedUpper (K : Type) [Field K] (neg : Bool) :=
  rootGroup CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K neg
abbrev Positive (K : Type) [Field K] := SignedUpper K false
abbrev Negative (K : Type) [Field K] := SignedUpper K true

theorem signedUpper_twist_map (K : Type) [Field K] (sigma : K≃+*K) (neg : Bool) :
    (SignedUpper K neg).map (unitTwist K sigma).toMonoidHom=SignedUpper K neg := by
  apply le_antisymm
  · apply Subgroup.map_le_iff_le_comap.mpr
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨⟨i,t⟩,rfl⟩
    change unitTwist K sigma (canonicalRoot rawData K neg i t)∈SignedUpper K neg
    rw [unitTwist_root]
    exact Subgroup.subset_closure ⟨(e6Permutation i,sigma t),rfl⟩
  · apply (Subgroup.closure_le _).mpr
    rintro g ⟨⟨i,t⟩,rfl⟩
    refine ⟨canonicalRoot rawData K neg (e6Permutation.symm i) (sigma.symm t),
      Subgroup.subset_closure ⟨(e6Permutation.symm i,sigma.symm t),rfl⟩,?_⟩
    change unitTwist K sigma
      (canonicalRoot rawData K neg (e6Permutation.symm i) (sigma.symm t))=_
    rw [unitTwist_root,Equiv.apply_symm_apply,RingEquiv.apply_symm_apply]

theorem positive_twist_map (K : Type) [Field K] (sigma : K≃+*K) :
    (Positive K).map (unitTwist K sigma).toMonoidHom=Positive K :=
  signedUpper_twist_map K sigma false

def positiveTwist (K : Type) [Field K] (sigma : K≃+*K) : MulAut (Positive K) :=
  ((unitTwist K sigma).subgroupMap (Positive K)).trans
    (MulEquiv.subgroupCongr (positive_twist_map K sigma))

theorem positiveTwist_val (K : Type) [Field K] (sigma : K≃+*K) (u : Positive K) :
    (positiveTwist K sigma u).val=unitTwist K sigma u.val := rfl

theorem positive_isPGroup (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    IsPGroup p (Positive K) :=
  CFSGNormTwoCoordinatePositivePGroup.rootGroup_isPGroup CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos E6Index K p false

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckPositiveTwist
