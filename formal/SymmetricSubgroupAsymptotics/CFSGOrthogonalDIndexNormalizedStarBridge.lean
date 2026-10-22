import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexResidualQuadraticCoordinates
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticShell

/-! The actual quadratic bridge in a normalized D star. The hypothesis
on the third companion is precisely the extra not-both-R11 condition.
It forces the residual vector to be singular; a quadratic shell then
provides a bridge over EVERY field, including F2. No hyperplane-avoidance
or odd-characteristic inference is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexNormalizedStarBridge
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexTailCoordinates CFSGOrthogonalDIndexResidualCorrection
open CFSGOrthogonalDIndexResidualDecomposition CFSGOrthogonalDIndexResidualQuadraticCoordinates
open CFSGOrthogonalDIndexQuadraticShell
variable (K : Type) [Field K]

theorem exists_bridge_vector (s : ℕ) (w t : Index (s + 4) → K)
    (hwQ : splitQuadraticForm K (s + 4) w = 0) (hw0 : w (Sum.inr 0) = 0)
    (hc : (splitQuadraticForm K (s + 4)).polarBilin w
      (Pi.single (Sum.inl (tailSecondIndex (s + 2))) 1) ≠ 0)
    (htQ : splitQuadraticForm K (s + 4) t = 0) (ht0 : t (Sum.inr 0) = 0)
    (htnot : ∀ a : K, t ≠ a • Pi.single (Sum.inl (0 : Fin (s + 4))) 1)
    (havoid : (splitQuadraticForm K (s + 4)).polarBilin
        (Pi.single (Sum.inl (tailSecondIndex (s + 2))) 1) t = 0 ∨
      (splitQuadraticForm K (s + 4)).polarBilin w t = 0) :
    ∃ d : Index (s + 4) → K,
      splitQuadraticForm K (s + 4) d = 0 ∧
      (splitQuadraticForm K (s + 4)).polarBilin
        (Pi.single (Sum.inl (0 : Fin (s + 4))) 1) d = 0 ∧
      (splitQuadraticForm K (s + 4)).polarBilin
        (Pi.single (Sum.inl (tailSecondIndex (s + 2))) 1) d ≠ 0 ∧
      (splitQuadraticForm K (s + 4)).polarBilin w d ≠ 0 ∧
      (splitQuadraticForm K (s + 4)).polarBilin t d ≠ 0 := by
  let Q := splitQuadraticForm K (s + 4)
  let R := splitQuadraticForm K (s + 2)
  let u : Index (s + 4) → K := Pi.single (Sum.inl 0) 1
  let v : Index (s + 4) → K := Pi.single (Sum.inl (tailSecondIndex (s + 2))) 1
  let j := residualMap K (s + 2) w
  let c := Q.polarBilin v w
  have hsym (x y : Index (s + 4) → K) : Q.polarBilin x y = Q.polarBilin y x :=
    QuadraticMap.polar_comm (Q : (Index (s + 4) → K) → K) x y
  have hc' : c ≠ 0 := by
    dsimp only [c]
    rwa [hsym v w]
  have hwv : Q.polarBilin w v = c := hsym w v
  obtain ⟨a, b, e, z, he⟩ := exists_residual_decomposition K (s + 2) w t hw0 hc ht0
  change t = a • u + b • v + e • w + j z at he
  have hvt : Q.polarBilin v t = e * c := by
    rw [he]
    exact axis_pairing_decomposition K (s + 2) w a b e z
  have hwt : Q.polarBilin w t = b * Q.polarBilin w v := by
    rw [he]
    exact companion_pairing_decomposition K (s + 2) w hwQ hw0 hc a b e z
  have hbe : b * e = 0 := by
    rcases havoid with hh | hh
    · have he0 : e = 0 := (mul_eq_zero.mp (hvt.symm.trans hh)).resolve_right hc'
      simp only [he0, mul_zero]
    · have hb0 : b = 0 := (mul_eq_zero.mp (hwt.symm.trans hh)).resolve_right hc
      simp only [hb0, zero_mul]
  have hzQ : R z = 0 := by
    have hh := quadratic_decomposition K (s + 2) w hwQ hw0 hc a b e z
    change Q (a • u + b • v + e • w + j z) = b * e * c + R z at hh
    rw [← he, htQ, hbe, zero_mul, zero_add] at hh
    exact hh.symm
  have hchoice : ∃ z' : Index (s + 2) → K,
      R z' = -c ∧ (b + e) * c + R.polarBilin z z' ≠ 0 := by
    by_cases hz : z = 0
    · refine ⟨shellVector K s (-c) 0, ?_, ?_⟩
      · exact (splitQuadraticForm_apply K (s + 2) _).trans
          (shellVector_quadratic K s (-c) 0)
      · have hsum : (b + e) * c ≠ 0 := by
          intro hh
          have hsum0 : b + e = 0 := (mul_eq_zero.mp hh).resolve_right hc'
          have hboth : b = 0 ∧ e = 0 := by
            rcases mul_eq_zero.mp hbe with hb | he0
            · exact ⟨hb, by simpa only [hb, zero_add] using hsum0⟩
            · exact ⟨by simpa only [he0, add_zero] using hsum0, he0⟩
          apply htnot a
          simpa only [hboth.1, hboth.2, hz, zero_smul, map_zero, add_zero] using he
        simpa only [hz, map_zero, LinearMap.zero_apply, add_zero] using hsum
    · obtain ⟨z', hQ, hB⟩ := exists_quadratic_polar_values K s z hz hzQ
        (-c) (1 - (b + e) * c)
      refine ⟨z', hQ, ?_⟩
      rw [hB]
      have hh : (b + e) * c + (1 - (b + e) * c) = (1 : K) := by ring
      rw [hh]
      exact one_ne_zero
  obtain ⟨z', hz'Q, hz'B⟩ := hchoice
  let d := v + w + j z'
  have hdQ : Q d = 0 := by
    have hh := quadratic_decomposition K (s + 2) w hwQ hw0 hc 0 1 1 z'
    change Q (0 • u + 1 • v + 1 • w + j z') = 1 * 1 * c + R z' at hh
    simpa only [zero_smul, zero_add, one_smul, one_mul, hz'Q, add_neg_cancel] using hh
  have hud : Q.polarBilin u d = 0 := by
    have huv : Q.polarBilin u v = 0 := axes_polar_zero K (s + 2)
    have huw : Q.polarBilin u w = 0 := (positive_polar K (s + 4) 0 w).trans hw0
    have huj : Q.polarBilin u (j z') = 0 :=
      residualMap_perp_positive K (s + 2) w z' _ (Or.inl rfl)
    simp only [d, map_add, huv, huw, huj, zero_add]
  have hvd : Q.polarBilin v d = c := by
    have hh := axis_pairing_decomposition K (s + 2) w 0 1 1 z'
    simpa only [zero_smul, zero_add, one_smul, one_mul] using hh
  have hwd : Q.polarBilin w d = c := by
    have hh := companion_pairing_decomposition K (s + 2) w hwQ hw0 hc 0 1 1 z'
    simp only [zero_smul, zero_add, one_smul, one_mul] at hh
    change Q.polarBilin w d = Q.polarBilin w v at hh
    exact hh.trans hwv
  have hjd : Q.polarBilin (j z) d = R.polarBilin z z' := by
    have hvj : Q.polarBilin (j z) v = 0 := (hsym _ _).trans
      (residualMap_perp_positive K (s + 2) w z _ (Or.inr rfl))
    have hwj : Q.polarBilin (j z) w = 0 := (hsym _ _).trans
      (residualMap_perp_companion K (s + 2) w hc z)
    simp only [d, map_add, hvj, hwj, zero_add]
    exact residualMap_polar K (s + 2) w z z'
  have htd : Q.polarBilin t d = (b + e) * c + R.polarBilin z z' := by
    rw [he]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      hud, hvd, hwd, hjd, smul_eq_mul, mul_zero, zero_add]
    ring
  exact ⟨d, hdQ, hud, (hvd.trans_ne hc'), (hwd.trans_ne hc'),
    htd.trans_ne hz'B⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexNormalizedStarBridge
