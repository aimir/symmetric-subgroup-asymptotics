import SymmetricSubgroupAsymptotics.CFSGTwistedA2HighestRootUnits
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! Two literal natural A2 derived words do not commute even projectively.
The middle coordinate is fixed, so a projective commutation scalar is
forced to be one. This includes q=3; no a^2 != 1 guard is required. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2HighestRootUnits
open CFSGTwistedANaturalMatrices
variable (K : Type) [Field K]

def delta (t a : K) : NaturalElementary K 2 := ⁅highest K (t * a), opposite K t⁻¹⁆

def deltaArray (t a : K) : Mat K 2 :=
  !![1 + a + a ^ 2, 0, -(t * a ^ 2);
     0, 1, 0;
     t⁻¹ * a, 0, 1 - a]

set_option maxHeartbeats 600000 in
theorem delta_val (t : K) (ht : t ≠ 0) (a : K) :
    ((delta K t a).val : Mat K 2) = deltaArray K t a := by
  have h : (delta K t a).val =
      ⁅entryUnit K (show (0 : Fin 3) ≠ 2 by decide) (t * a),
        entryUnit K (show (2 : Fin 3) ≠ 0 by decide) t⁻¹⁆ := by
    change ⁅(highest K (t * a)).val, (opposite K t⁻¹).val⁆ = _
    rw [highest_val, opposite_val]
  rw [h, commutatorElement_def]
  simp only [Units.val_mul, entryUnit_val, entryUnit_inv_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [deltaArray, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single,
      Matrix.one_apply] <;> field_simp [ht] <;> ring

theorem delta_commutator_not_scalar (t : K) (ht : t ≠ 0)
    (a : K) (ha : a ≠ 0) (haone : a ≠ 1) :
    ¬ ∃ c : K, ((⁅delta K t 1, delta K t a⁆).val : Mat K 2) = c • 1 := by
  rintro ⟨c, hc⟩
  let u := delta K t 1
  let v := delta K t a
  have hcancel : ⁅u, v⁆ * (v * u) = u * v := by
    simp only [commutatorElement_def, mul_assoc, inv_mul_cancel_left,
      inv_mul_cancel, mul_one]
  have he := congrArg (fun w : NaturalElementary K 2 => (w.val : Mat K 2)) hcancel
  change ((⁅u, v⁆).val : Mat K 2) *
    ((v.val : Mat K 2) * (u.val : Mat K 2)) =
      (u.val : Mat K 2) * (v.val : Mat K 2) at he
  change ((⁅u, v⁆).val : Mat K 2) = c • 1 at hc
  rw [hc, smul_mul_assoc, one_mul] at he
  have hmiddle := congrArg (fun M : Mat K 2 => M 1 1) he
  have hlast := congrArg (fun M : Mat K 2 => M 2 2) he
  dsimp only [u, v] at hmiddle hlast
  simp [delta_val K t ht, Matrix.mul_apply, Fin.sum_univ_three,
    deltaArray] at hmiddle hlast
  have hc1 : c = 1 := by simpa using hmiddle
  rw [hc1] at hlast
  field_simp [ht] at hlast
  exact haone hlast.symm


end SymmetricSubgroupAsymptotics.CFSGTwistedA2HighestRootUnits
