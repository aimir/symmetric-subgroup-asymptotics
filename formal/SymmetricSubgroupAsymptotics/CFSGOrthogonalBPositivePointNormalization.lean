import SymmetricSubgroupAsymptotics.CFSGOrthogonalBPositiveLinearLift
import SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints

/-! The inverse of the literal special-isometry extension normalizes
an actual positive-space projective representative. Every SAME original
positive singular point is then fixed, while the opposite negative
space remains preserved. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBPositivePointNormalization
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBPositiveSubspace
open CFSGOrthogonalBOpposedGraphShear CFSGOrthogonalBSpecialFormGroup
open CFSGOrthogonalBPositiveLinearLift CFSGPolarSubspacePoints
variable (K : Type) [Field K]

theorem exists_special_point_normalization (n : ℕ)
    (L : positiveSubspace K n →ₗ[K] (Index n → K))
    (hL : Function.Injective L) (hRange : L.range = positiveSubspace K n)
    (f : Points (gram K n).toBilin' ≃ Points (gram K n).toBilin')
    (hrep : ∀ R : Points (gram K n).toBilin', ∀ hR : R.val ≤ positiveSubspace K n,
      ∀ v : Index n → K, ∀ hv : v ∈ R.val, L ⟨v, hR hv⟩ ∈ (f R).val) :
    ∃ a : specialFormUnits K n,
      (∀ R : Points (gram K n).toBilin', R.val ≤ positiveSubspace K n →
        (f R).val.map (a.val : Mat K n).mulVecLin = R.val) ∧
      (negativeSubspace K n).map (a.val : Mat K n).mulVecLin = negativeSubspace K n := by
  obtain ⟨g, hg, hneg⟩ := exists_special_extension K n L hL hRange
  let u := g.val
  let invMap := (((u⁻¹ : (Mat K n)ˣ) : Mat K n)).mulVecLin
  have hleft (v : Index n → K) :
      (((u⁻¹ : (Mat K n)ˣ) : Mat K n)) *ᵥ ((u : Mat K n) *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hcomp : invMap.comp (u : Mat K n).mulVecLin = LinearMap.id := by
    apply LinearMap.ext
    exact hleft
  have hnegInv : (negativeSubspace K n).map invMap = negativeSubspace K n := by
    have he := congrArg (fun T : Submodule K (Index n → K) => T.map invMap) hneg
    change ((negativeSubspace K n).map (u : Mat K n).mulVecLin).map invMap =
      (negativeSubspace K n).map invMap at he
    rw [← Submodule.map_comp, hcomp, Submodule.map_id] at he
    exact he.symm
  refine ⟨g⁻¹, ?_, hnegInv⟩
  intro R hR
  change (f R).val.map invMap = R.val
  have hle : R.val ≤ (f R).val.map invMap := by
    intro v hv
    refine ⟨L ⟨v, hR hv⟩, hrep R hR v hv, ?_⟩
    change (((u⁻¹ : (Mat K n)ˣ) : Mat K n)) *ᵥ L ⟨v, hR hv⟩ = v
    calc
      _ = (((u⁻¹ : (Mat K n)ˣ) : Mat K n)) *ᵥ ((u : Mat K n) *ᵥ v) :=
        congrArg (fun x => (((u⁻¹ : (Mat K n)ˣ) : Mat K n)) *ᵥ x) (hg ⟨v, hR hv⟩).symm
      _ = v := hleft v
  let e := (Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Index n → K))) (u⁻¹)
  have hd : Module.finrank K ((f R).val.map invMap) = 1 := by
    change Module.finrank K ((f R).val.map e.toLinearMap) = 1
    exact (e.finrank_map_eq (f R).val).trans (f R).property.1
  exact (Submodule.eq_of_le_of_finrank_le hle (by rw [hd, R.property.1])).symm

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBPositivePointNormalization
