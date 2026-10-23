import SymmetricSubgroupAsymptotics.CFSGHermitianSimilitudeCardinality
import SymmetricSubgroupAsymptotics.CFSGHermitianIsometryDeterminant
import SymmetricSubgroupAsymptotics.CFSGProjectiveLinearPointAction

/-! The determinant fibre of the actual Hermitian isometry group.
Together with the multiplier fibre this bounds literal linear
similitudes by the special isometries and two scalar unit groups. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHermitianSimilitudeGroup
open CFSGTwistedAUnitaryParameters
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

def isometryMatrixHom (sigma : K ≃+* K) (H : (Matrix I I K)ˣ) :
    isometries sigma H →* Matrix.GeneralLinearGroup I K :=
  CFSGProjectiveLinearPointAction.linearEquiv.symm.toMonoidHom.comp (isometries sigma H).subtype

def isometryDeterminantHom (sigma : K ≃+* K) (H : (Matrix I I K)ˣ) :
    isometries sigma H →* Kˣ := Matrix.GeneralLinearGroup.det.comp (isometryMatrixHom sigma H)

def unitNormHom (sigma : K ≃+* K) : Kˣ →* Kˣ :=
  (Units.map sigma.toMonoidHom) * MonoidHom.id Kˣ

def normOneUnits (sigma : K ≃+* K) : Subgroup Kˣ := (unitNormHom sigma).ker

theorem isometryDeterminant_norm_one (sigma : K ≃+* K) (H : (Matrix I I K)ˣ)
    (e : isometries sigma H) : isometryDeterminantHom sigma H e ∈ normOneUnits sigma := by
  apply Units.ext
  change sigma (Matrix.det (isometryMatrixHom sigma H e : Matrix I I K)) *
    Matrix.det (isometryMatrixHom sigma H e : Matrix I I K) = 1
  apply CFSGHermitianIsometryDeterminant.determinant_norm_one
  intro v w
  change hermitianPair sigma H
    (CFSGProjectiveLinearPointAction.linearEquiv (isometryMatrixHom sigma H e) v)
    (CFSGProjectiveLinearPointAction.linearEquiv (isometryMatrixHom sigma H e) w) = _
  change hermitianPair sigma H
    (CFSGProjectiveLinearPointAction.linearEquiv
      (CFSGProjectiveLinearPointAction.linearEquiv.symm e.val) v)
    (CFSGProjectiveLinearPointAction.linearEquiv
      (CFSGProjectiveLinearPointAction.linearEquiv.symm e.val) w) = _
  rw [CFSGProjectiveLinearPointAction.linearEquiv.apply_symm_apply]
  exact e.property v w

def normOneDeterminantHom (sigma : K ≃+* K) (H : (Matrix I I K)ˣ) :
    isometries sigma H →* normOneUnits sigma :=
  (isometryDeterminantHom sigma H).codRestrict (normOneUnits sigma)
    (isometryDeterminant_norm_one sigma H)

def specialIsometries (sigma : K ≃+* K) (H : (Matrix I I K)ˣ) :
    Subgroup (isometries sigma H) := (isometryDeterminantHom sigma H).ker

theorem isometries_card_le_special [Finite K] (sigma : K ≃+* K) (H : (Matrix I I K)ˣ) :
    Nat.card (isometries sigma H) ≤ Nat.card (specialIsometries sigma H) * Nat.card (normOneUnits sigma) := by
  let f := normOneDeterminantHom sigma H
  have hk : f.ker = specialIsometries sigma H := MonoidHom.ker_codRestrict _ _ _
  have hr : Nat.card f.range ≤ Nat.card (normOneUnits sigma) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  calc
    Nat.card (isometries sigma H) = Nat.card f.ker * Nat.card f.range := by
      rw [← f.ker.card_mul_index, Subgroup.index_ker]
    _ ≤ Nat.card (specialIsometries sigma H) * Nat.card (normOneUnits sigma) := by
      rw [hk]
      exact Nat.mul_le_mul_left _ hr

theorem similitudes_card_le_special [Finite K] (sigma : K ≃+* K)
    (hsigma : ∀ x, sigma (sigma x) = x) (eps : K) (H : (Matrix I I K)ˣ)
    (hH : (H : Matrix I I K).map sigma = eps • (H : Matrix I I K).transpose) (i₀ : I) :
    Nat.card (similitudes sigma H) ≤
      Nat.card (specialIsometries sigma H) * Nat.card (normOneUnits sigma) * Nat.card (fixedUnits sigma) :=
  (similitudes_card_le sigma hsigma eps H hH i₀).trans
    (Nat.mul_le_mul_right _ (isometries_card_le_special sigma H))

end SymmetricSubgroupAsymptotics.CFSGHermitianSimilitudeGroup
