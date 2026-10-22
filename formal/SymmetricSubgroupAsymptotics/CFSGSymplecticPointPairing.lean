import SymmetricSubgroupAsymptotics.CFSGSymplecticPolarity
import SymmetricSubgroupAsymptotics.CFSGProjectiveFieldAction

/-! The literal alternating zero-pairing relation is well-defined on
projective points and preserved by every coordinate field automorphism. -/
set_option autoImplicit false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticPointPairing
open CFSGSymplecticSerreMatrices CFSGSymplecticTransvectionGeometry CFSGSymplecticPolarity
variable {K : Type} [Field K]

theorem orthogonal_mk (n : ℕ) (v w : Index n → K) (hv : v ≠ 0) (hw : w ≠ 0) :
    Orthogonal K n (Projectivization.mk K v hv) (Projectivization.mk K w hw) ↔
      pairing n v w = 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep K v hv
  obtain ⟨b, hb⟩ := Projectivization.exists_smul_eq_mk_rep K w hw
  unfold Orthogonal
  rw [← ha, ← hb]
  change pairing n ((a : K) • v) ((b : K) • w) = 0 ↔ pairing n v w = 0
  rw [pairing_smul_left, pairing_smul_right]
  simp only [mul_eq_zero, a.ne_zero, b.ne_zero, false_or]

theorem field_pairing (n : ℕ) (s : K ≃+* K) (v w : Index n → K) :
    pairing n (s ∘ v) (s ∘ w) = s (pairing n v w) := by
  simp only [pairing, map_sum, map_sub, map_mul, Function.comp_apply]

theorem fieldPoint_orthogonal (n : ℕ) (s : K ≃+* K)
    (p q : CFSGSymplecticPolarity.Points K n) :
    Orthogonal K n (CFSGProjectiveFieldAction.pointEquiv s p)
      (CFSGProjectiveFieldAction.pointEquiv s q) ↔ Orthogonal K n p q := by
  induction p using Projectivization.ind with
  | h v hv =>
    induction q using Projectivization.ind with
    | h w hw =>
      rw [CFSGProjectiveFieldAction.pointEquiv_mk, CFSGProjectiveFieldAction.pointEquiv_mk,
        orthogonal_mk, orthogonal_mk, field_pairing]
      exact map_eq_zero s

end SymmetricSubgroupAsymptotics.CFSGSymplecticPointPairing
