import SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
import Mathlib.Tactic.Ring

/-! The standard alternating pairing on the SAME paired natural
coordinates used by the literal elementary C model. These identities
hold in every characteristic, with no nondegeneracy assumption hidden
in an abstract form record. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticTransvectionGeometry
open CFSGSymplecticSerreMatrices
variable {K : Type} [Field K]

def pairing (r : ℕ) (v w : Index r → K) : K :=
  ∑ i : Fin r, (v (Sum.inl i) * w (Sum.inr i) - v (Sum.inr i) * w (Sum.inl i))

@[simp] theorem pairing_self (r : ℕ) (v : Index r → K) : pairing r v v = 0 := by
  simp [pairing, mul_comm]

theorem pairing_swap (r : ℕ) (v w : Index r → K) : pairing r v w = -pairing r w v := by
  unfold pairing
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem pairing_add_left (r : ℕ) (u v w : Index r → K) :
    pairing r (u + v) w = pairing r u w + pairing r v w := by
  unfold pairing
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.add_apply]
  ring

theorem pairing_add_right (r : ℕ) (u v w : Index r → K) :
    pairing r u (v + w) = pairing r u v + pairing r u w := by
  unfold pairing
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.add_apply]
  ring

theorem pairing_smul_left (r : ℕ) (c : K) (v w : Index r → K) :
    pairing r (c • v) w = c * pairing r v w := by
  unfold pairing
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem pairing_smul_right (r : ℕ) (c : K) (v w : Index r → K) :
    pairing r v (c • w) = c * pairing r v w := by
  unfold pairing
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

@[simp] theorem pairing_zero_left (r : ℕ) (v : Index r → K) : pairing r 0 v = 0 := by
  simp [pairing]

@[simp] theorem pairing_zero_right (r : ℕ) (v : Index r → K) : pairing r v 0 = 0 := by
  simp [pairing]

theorem pairing_pos_basis (r : ℕ) (v : Index r → K) (i : Fin r) :
    pairing r v (Pi.single (Sum.inl i) 1) = -v (Sum.inr i) := by
  simp [pairing, Pi.single_apply]

theorem pairing_neg_basis (r : ℕ) (v : Index r → K) (i : Fin r) :
    pairing r v (Pi.single (Sum.inr i) 1) = v (Sum.inl i) := by
  simp [pairing, Pi.single_apply]

theorem exists_pairing_ne_zero (r : ℕ) (v : Index r → K) (hv : v ≠ 0) :
    ∃ w : Index r → K, pairing r v w ≠ 0 := by
  have hx : ∃ i, v i ≠ 0 := by
    by_contra h
    apply hv
    funext i
    exact not_ne_iff.mp (not_exists.mp h i)
  obtain ⟨i, hi⟩ := hx
  cases i with
  | inl i => exact ⟨Pi.single (Sum.inr i) 1, by simpa only [pairing_neg_basis] using hi⟩
  | inr i => exact ⟨Pi.single (Sum.inl i) 1, by simpa only [pairing_pos_basis, neg_ne_zero] using hi⟩

end SymmetricSubgroupAsymptotics.CFSGSymplecticTransvectionGeometry
