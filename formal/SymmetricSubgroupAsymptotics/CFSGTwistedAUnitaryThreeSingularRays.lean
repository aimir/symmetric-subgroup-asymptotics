import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryStarPoints
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCentralParameters
import Mathlib.Tactic.LinearCombination

/-! Three distinct literal singular rays in every unitary space of
dimension at least two, including q=2. A nonzero central parameter
supplies the third ray; no residue cardinality or group recognition
is assumed. These are the thickness witnesses for rank-two residues. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGTwistedAUnitaryNaturalRadical
open CFSGTwistedAUnitaryParameters

def unitaryEndpointVector (q : CFSG.PrimePower) (r : ℕ) (v : Fin 2 → q.Extension 2) :
    Fin (r + 1) → q.Extension 2 :=
  v 0 • Pi.single 0 1 + v 1 • Pi.single (Fin.last r) 1

theorem unitaryEndpointVector_first (q : CFSG.PrimePower) (r : ℕ) (hr : 1 ≤ r)
    (v : Fin 2 → q.Extension 2) : unitaryEndpointVector q r v 0 = v 0 := by
  have hn : (0 : Fin (r + 1)) ≠ Fin.last r := by intro h; have := congrArg Fin.val h; simp only [Fin.val_zero, Fin.val_last] at this; omega
  simp only [unitaryEndpointVector, Pi.add_apply, Pi.smul_apply, Pi.single_apply,
    ite_true, if_neg hn, smul_eq_mul, mul_one, mul_zero, add_zero]

theorem unitaryEndpointVector_last (q : CFSG.PrimePower) (r : ℕ) (hr : 1 ≤ r)
    (v : Fin 2 → q.Extension 2) : unitaryEndpointVector q r v (Fin.last r) = v 1 := by
  have hn : Fin.last r ≠ (0 : Fin (r + 1)) := by intro h; have := congrArg Fin.val h; simp only [Fin.val_zero, Fin.val_last] at this; omega
  simp only [unitaryEndpointVector, Pi.add_apply, Pi.smul_apply, Pi.single_apply,
    if_neg hn, ite_true, smul_eq_mul, mul_one, mul_zero, zero_add]

theorem unitaryEndpointVector_pair (q : CFSG.PrimePower) (r : ℕ) (hr : 1 ≤ r)
    (v w : Fin 2 → q.Extension 2) :
    unitaryNaturalPair q r (unitaryEndpointVector q r v) (unitaryEndpointVector q r w) =
      definingFieldAutomorphism q 2 (v 0) * w 1 +
        (-1 : q.Extension 2) ^ r * definingFieldAutomorphism q 2 (v 1) * w 0 := by
  have h0 := hermitianPair_smul (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r)
    (v 0) 1 (Pi.single (0 : Fin (r + 1)) 1) (unitaryEndpointVector q r w)
  have h1 := hermitianPair_smul (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r)
    (v 1) 1 (Pi.single (Fin.last r) 1) (unitaryEndpointVector q r w)
  simp only [one_smul, mul_one] at h0 h1
  change hermitianPair _ _ (_ + _) _ = _
  rw [hermitianPair_add_left, h0, h1]
  change definingFieldAutomorphism q 2 (v 0) *
      unitaryNaturalPair q r (Pi.single (0 : Fin (r + 1)) 1) (unitaryEndpointVector q r w) +
    definingFieldAutomorphism q 2 (v 1) *
      unitaryNaturalPair q r (Pi.single (Fin.last r) 1) (unitaryEndpointVector q r w) = _
  rw [unitaryNaturalPair_basis, unitaryNaturalPair_basis, Fin.rev_zero, Fin.rev_last,
    unitaryEndpointVector_first q r hr, unitaryEndpointVector_last q r hr]
  have hsign0 : signWeight (q.Extension 2) r (0 : Fin (r + 1)) = 1 := rfl
  have hsignL : signWeight (q.Extension 2) r (Fin.last r) = (-1 : q.Extension 2) ^ r := rfl
  rw [hsign0, hsignL]
  ring

theorem unitaryEndpointVector_span_ne (q : CFSG.PrimePower) (r : ℕ) (hr : 1 ≤ r)
    (v w : Fin 2 → q.Extension 2) (hdet : v 0 * w 1 - v 1 * w 0 ≠ 0) :
    ((q.Extension 2) ∙ unitaryEndpointVector q r v : Submodule (q.Extension 2) _) ≠
      (q.Extension 2) ∙ unitaryEndpointVector q r w := by
  intro he
  obtain ⟨c, hc⟩ := Submodule.span_singleton_eq_span_singleton.mp he
  have h0 := congrFun hc 0
  have h1 := congrFun hc (Fin.last r)
  change (c : q.Extension 2) * unitaryEndpointVector q r v 0 = unitaryEndpointVector q r w 0 at h0
  change (c : q.Extension 2) * unitaryEndpointVector q r v (Fin.last r) =
    unitaryEndpointVector q r w (Fin.last r) at h1
  rw [unitaryEndpointVector_first q r hr, unitaryEndpointVector_first q r hr] at h0
  rw [unitaryEndpointVector_last q r hr, unitaryEndpointVector_last q r hr] at h1
  apply hdet
  rw [← h0, ← h1]
  ring

theorem exists_three_unitary_singular_rays (q : CFSG.PrimePower) (r : ℕ) (hr : 1 ≤ r) :
    ∃ u v w : Fin (r + 1) → q.Extension 2,
      u ≠ 0 ∧ v ≠ 0 ∧ w ≠ 0 ∧
      unitaryNaturalPair q r u u = 0 ∧ unitaryNaturalPair q r v v = 0 ∧
      unitaryNaturalPair q r w w = 0 ∧
      ((q.Extension 2) ∙ u : Submodule (q.Extension 2) _) ≠ (q.Extension 2) ∙ v ∧
      ((q.Extension 2) ∙ u : Submodule (q.Extension 2) _) ≠ (q.Extension 2) ∙ w ∧
      ((q.Extension 2) ∙ v : Submodule (q.Extension 2) _) ≠ (q.Extension 2) ∙ w := by
  obtain ⟨t, ht, htc⟩ := exists_nonzero_central_parameter q r
  have htparam := (centralCondition_iff q r t).mp htc
  change definingFieldAutomorphism q 2 t + (-1 : q.Extension 2) ^ r * t = 0 at htparam
  have heps : (-1 : q.Extension 2) ^ r * (-1 : q.Extension 2) ^ r = 1 := by
    rw [← mul_pow]
    simp
  have hnorm : t + (-1 : q.Extension 2) ^ r * definingFieldAutomorphism q 2 t = 0 := by
    linear_combination ((-1 : q.Extension 2) ^ r) * htparam - t * heps
  let u := unitaryEndpointVector q r ![1, 0]
  let v := unitaryEndpointVector q r ![0, 1]
  let w := unitaryEndpointVector q r ![1, t]
  have hu : u ≠ 0 := by
    intro h
    have hh := congrFun h 0
    simpa only [u, unitaryEndpointVector_first q r hr, Matrix.cons_val_zero, Pi.zero_apply, one_ne_zero] using hh
  have hv : v ≠ 0 := by
    intro h
    have hh := congrFun h (Fin.last r)
    simpa only [v, unitaryEndpointVector_last q r hr, Matrix.cons_val_one, Matrix.cons_val_zero,
      Pi.zero_apply, one_ne_zero] using hh
  have hw : w ≠ 0 := by
    intro h
    have hh := congrFun h 0
    simpa only [w, unitaryEndpointVector_first q r hr, Matrix.cons_val_zero, Pi.zero_apply, one_ne_zero] using hh
  refine ⟨u, v, w, hu, hv, hw, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [unitaryEndpointVector_pair q r hr]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_one, map_zero, mul_zero, zero_mul, add_zero]
  · rw [unitaryEndpointVector_pair q r hr]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_one, map_zero, mul_zero, zero_mul, zero_add]
  · rw [unitaryEndpointVector_pair q r hr]
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, map_one, one_mul, mul_one] using hnorm
  · apply unitaryEndpointVector_span_ne q r hr
    norm_num
  · apply unitaryEndpointVector_span_ne q r hr
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, zero_mul, sub_zero] using ht
  · apply unitaryEndpointVector_span_ne q r hr
    norm_num

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
