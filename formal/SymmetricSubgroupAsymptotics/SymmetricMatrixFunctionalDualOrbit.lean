import SymmetricSubgroupAsymptotics.SymmetricMatrixFunctionalReconstruction
import SymmetricSubgroupAsymptotics.CharacteristicTwoQuadraticIsometryIndex
import SymmetricSubgroupAsymptotics.InvariantAnnihilatorOrbitIndex

/-! The SAME actual F-functional stabilizer embeds in the actual
quadratic-isometry subgroup. Its contragredient orbit therefore inherits
the exact two-frame index lower bound, with no K-linearity premise
on the original F-linear functional. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.SymmetricMatrixFunctionalDualOrbit

open SymmetricMatrixCongruenceAction SymmetricMatrixQuadraticFunctional
open SymmetricMatrixFunctionalReconstruction QuadraticIsometryPairOrbitCardinality
variable {F K : Type*} [Field F] [Field K] [Algebra F K] (n : ℕ)

def restrictedCongruence :
    GeneralLinear (K := K) n →* Space (K := K) n ≃ₗ[F] Space (K := K) n where
  toFun A := (congruence n A).restrictScalars F
  map_one' := by
    apply LinearEquiv.ext
    intro S
    change congruenceLinearMap n 1 S = S
    exact congruenceLinearMap_one n S
  map_mul' A B := by
    apply LinearEquiv.ext
    intro S
    change congruenceLinearMap n (A * B) S =
      congruenceLinearMap n A (congruenceLinearMap n B S)
    exact congruenceLinearMap_mul n A B S

def matrixLinearEquiv : GeneralLinear (K := K) n ≃*
    ((Fin n → K) ≃ₗ[K] (Fin n → K)) :=
  Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin n → K))

@[simp] theorem matrixLinearEquiv_apply (A : GeneralLinear (K := K) n) (v : Fin n → K) :
    matrixLinearEquiv n A v = A.val *ᵥ v := rfl

local instance congruenceDualAction :
    MulAction (GeneralLinear (K := K) n) (Module.Dual F (Space (K := K) n)) :=
  InvariantAnnihilatorOrbitIndex.dualAction (restrictedCongruence (F := F) n)

private theorem dual_stabilizer_eq (ℓ : Module.Dual F (Space (K := K) n)) :
    MulAction.stabilizer (GeneralLinear (K := K) n) ℓ = stabilizer n ℓ := by
  ext A
  constructor
  · intro hA S
    change ℓ.comp ((restrictedCongruence (F := F) n) A⁻¹).toLinearMap = ℓ at hA
    have he := congrArg (fun φ : Module.Dual F (Space (K := K) n) =>
      φ (congruenceLinearMap n A S)) hA
    change ℓ (congruenceLinearMap n A⁻¹ (congruenceLinearMap n A S)) =
      ℓ (congruenceLinearMap n A S) at he
    rw [← congruenceLinearMap_mul, inv_mul_cancel, congruenceLinearMap_one] at he
    exact he.symm
  · intro hA
    change ℓ.comp ((restrictedCongruence (F := F) n) A⁻¹).toLinearMap = ℓ
    apply LinearMap.ext
    intro S
    have hi : A⁻¹ ∈ stabilizer n ℓ := (stabilizer n ℓ).inv_mem hA
    exact hi S

/-- The lower bound is for the orbit of the actual entire functional. -/
theorem two_frame_le_twice_dual_orbit [Finite K] [CharP K 2] [Module.Finite F K]
    (hn : 2 ≤ n) (f : Module.Dual F K) (hf : f ≠ 0)
    (ℓ : Module.Dual F (Space (K := K) n)) (x y : Fin n → K)
    (hnorm : ∀ t : K, ℓ (t • cross n x y) = f t) :
    (Nat.card K - 1) * Nat.card K ^ (n - 2) * (Nat.card K ^ n - Nat.card K) ≤
      2 * Nat.card (InvariantAnnihilatorOrbitIndex.dualOrbit
        (restrictedCongruence (F := F) n) ℓ) := by
  letI : Finite ((Fin n → K) ≃ₗ[K] (Fin n → K)) := Finite.of_injective
    (fun e : (Fin n → K) ≃ₗ[K] (Fin n → K) => (e : (Fin n → K) → (Fin n → K)))
    DFunLike.coe_injective
  obtain ⟨L, hL, hpolar⟩ := exists_normalized_lift n f hf ℓ x y hnorm
  let Q := quadratic n L
  let S := stabilizer n ℓ
  let E := matrixLinearEquiv (K := K) n
  have hmap : S.map E.toMonoidHom ≤ isometries Q := by
    intro g hg
    obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp hg
    intro v
    change quadratic n L (A.val *ᵥ v) = quadratic n L v
    exact stabilizer_preserves_quadratic n f hf ℓ L hL ⟨A, hA⟩ v
  have hidx : (S.map E.toMonoidHom).index = S.index := S.index_map_equiv E
  have hle : (isometries Q).index ≤ S.index := by
    rw [← hidx]
    exact Nat.le_of_dvd
      (Nat.pos_of_ne_zero (S.map E.toMonoidHom).index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hmap)
  have hQ : (Nat.card K - 1) * Nat.card K ^ (n - 2) *
      (Nat.card K ^ n - Nat.card K) ≤ 2 * (isometries Q).index := by
    have he := CharacteristicTwoQuadraticIsometryIndex.two_frame_le_twice_index_of_polar_one
      Q (by simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hn)
      x y hpolar
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using he
  have hOrbit : S.index = Nat.card (InvariantAnnihilatorOrbitIndex.dualOrbit
      (restrictedCongruence (F := F) n) ℓ) := by
    change (stabilizer n ℓ).index = _
    rw [← dual_stabilizer_eq n ℓ]
    exact (Nat.card_congr
      (MulAction.orbitEquivQuotientStabilizer (GeneralLinear (K := K) n) ℓ)).symm
  calc
    _ ≤ 2 * (isometries Q).index := hQ
    _ ≤ 2 * S.index := Nat.mul_le_mul_left 2 hle
    _ = _ := congrArg (fun k : ℕ => 2 * k) hOrbit

end SymmetricSubgroupAsymptotics.SymmetricMatrixFunctionalDualOrbit
