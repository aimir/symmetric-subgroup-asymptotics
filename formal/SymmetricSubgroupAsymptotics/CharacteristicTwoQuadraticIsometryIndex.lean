import SymmetricSubgroupAsymptotics.QuadraticIsometryPairOrbitCardinality
import SymmetricSubgroupAsymptotics.GeneralLinearTwoFrameCardinality
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! Fraction-free exact cancellation of the actual two-frame count.
This bounds the index of the actual quadratic-isometry subgroup of
GL(V), allowing an arbitrary radical of the quadratic form. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped LinearAlgebra.Projectivization

namespace SymmetricSubgroupAsymptotics.CharacteristicTwoQuadraticIsometryIndex

open QuadraticIsometryPairOrbitCardinality GeneralLinearTwoFrameCardinality
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

local instance finiteLinearEquiv [Finite V] : Finite (V ≃ₗ[K] V) :=
  Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V)) DFunLike.coe_injective

/-- The exact two-frame numerator; no replacement by a weaker q-power
or classification of the form is used in the cancellation. -/
theorem two_frame_le_twice_index [Finite K] [Finite V] [CharP K 2]
    (Q : QuadraticForm K V) (hd : 2 ≤ Module.finrank K V)
    (u w : V) (hu : Q u ≠ 0) (huw : Q.polarBilin u w = 1) :
    (Nat.card K - 1) * Nat.card K ^ (Module.finrank K V - 2) *
      (Nat.card K ^ Module.finrank K V - Nat.card K) ≤
        2 * (isometries Q).index := by
  letI : Module.Finite K V := Module.Finite.of_finite
  let q := Nat.card K
  let d := Module.finrank K V
  let P := Nat.card (ℙ K V)
  let R := BilinearPairFixerRestriction.complement Q.polarBilin u w
  let C := Nat.card (R ≃ₗ[K] R)
  let S := isometries Q
  have hzero (v : V) : Q.polarBilin v v = 0 := by
    change QuadraticMap.polar Q v v = 0
    rw [QuadraticMap.polar_self]
    exact CharTwo.two_nsmul _
  have hwu : Q.polarBilin w u = 1 := by
    change QuadraticMap.polar Q w u = 1
    rw [QuadraticMap.polar_comm]
    exact huw
  have hR : Module.finrank K R = d - 2 :=
    BilinearPairFixerRestriction.complement_finrank Q.polarBilin u w (hzero u) huw hwu
  have hC : C = orderProduct q (d - 2) := by
    change Nat.card (R ≃ₗ[K] R) = _
    rw [linearEquiv_card_eq_orderProduct, hR]
  have hG : Nat.card (V ≃ₗ[K] V) =
      (q ^ d - 1) * (q ^ d - q) * q ^ (2 * (d - 2)) * C := by
    rw [linearEquiv_card_eq_orderProduct]
    change orderProduct q d = _
    have he : d - 2 + 2 = d := by dsimp only [d]; omega
    have hr := orderProduct_add_two q (d - 2)
    rw [he, ← hC] at hr
    exact hr
  have hS : Nat.card S ≤ P * (2 * q ^ (d - 2)) * C :=
    card_le_projective_mul_polar_fibre_mul_complement Q u w hu huw
  have hP : q ^ d - 1 = P * (q - 1) := by
    have he := Projectivization.card K V
    rw [Module.natCard_eq_pow_finrank (K := K) (V := V)] at he
    exact he
  have hune : u ≠ 0 := by
    intro he
    exact hu (by rw [he, map_zero])
  letI : Nonempty (ℙ K V) := ⟨Projectivization.mk K u hune⟩
  have hPpos : 0 < P := Nat.card_pos
  have hCpos : 0 < C := Nat.card_pos
  have hqpos : 0 < q := Nat.card_pos
  let F := P * q ^ (d - 2) * C
  have hFpos : 0 < F := Nat.mul_pos (Nat.mul_pos hPpos (pow_pos hqpos _)) hCpos
  have hp : q ^ (2 * (d - 2)) = q ^ (d - 2) * q ^ (d - 2) := by
    rw [two_mul, pow_add]
  have hmul : ((q - 1) * q ^ (d - 2) * (q ^ d - q)) * F ≤
      (2 * S.index) * F := by
    calc
      _ = Nat.card (V ≃ₗ[K] V) := by rw [hG, hP, hp]; dsimp only [F]; ring
      _ = S.index * Nat.card S := S.index_mul_card.symm
      _ ≤ S.index * (P * (2 * q ^ (d - 2)) * C) := Nat.mul_le_mul_left _ hS
      _ = (2 * S.index) * F := by dsimp only [F]; ring
  exact Nat.le_of_mul_le_mul_right hmul hFpos

/-- A normalized actual polar coefficient suffices; the nonzero-level
pair is constructed by the checked three-vector argument. -/
theorem two_frame_le_twice_index_of_polar_one [Finite K] [Finite V] [CharP K 2]
    (Q : QuadraticForm K V) (hd : 2 ≤ Module.finrank K V)
    (x y : V) (hxy : Q.polarBilin x y = 1) :
    (Nat.card K - 1) * Nat.card K ^ (Module.finrank K V - 2) *
      (Nat.card K ^ Module.finrank K V - Nat.card K) ≤
        2 * (isometries Q).index := by
  obtain ⟨u, w, hu, huw⟩ := exists_nonzero_level_pair Q x y hxy
  exact two_frame_le_twice_index Q hd u w hu huw

end SymmetricSubgroupAsymptotics.CharacteristicTwoQuadraticIsometryIndex
