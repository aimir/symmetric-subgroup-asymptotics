import SymmetricSubgroupAsymptotics.CFSGUnitaryHermitianPolynomial
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryProjectivePointIndex
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryNaturalMiddle

/-! The polynomial's zero condition is the actual signed-form condition,
and every literal defining-fixed first column satisfies it. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGUnitaryHermitianPolynomial
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryCoordinates CFSGSerreOrdinaryTwists

theorem signedNorm_eq_dot (q : CFSG.PrimePower) (r : ℕ)
    (v : Fin (r + 1) → q.Extension 2) :
    signedNorm q r v = dotProduct (definingFieldAutomorphism q 2 ∘ v)
      ((signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) *ᵥ v) := by
  simp only [signedNorm, dotProduct, Matrix.mulVec, signedReversalUnit_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_comm, mul_left_comm]

theorem signedNorm_first_column_zero (q : CFSG.PrimePower) (r : ℕ) (hr : 1 ≤ r)
    (g : naturalFixed r q) :
    signedNorm q r (fun i => (g.val.val : Mat (q.Extension 2) r) i 0) = 0 := by
  let A := (g.val.val : Mat (q.Extension 2) r)
  let J := (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r)
  have h := fixed_unit_signedForm (q.Extension 2) r
    (definingFieldAutomorphism q 2).toRingHom g.val.val g.property
  have he := congrArg (fun M : Mat (q.Extension 2) r => M 0 0) h
  have hd : dotProduct (definingFieldAutomorphism q 2 ∘ fun i => A i 0)
      (J *ᵥ fun i => A i 0) =
      (((A.map (definingFieldAutomorphism q 2)).transpose * J * A) 0 0) := by
    rw [mul_assoc]
    rfl
  rw [signedNorm_eq_dot]
  have hz : J 0 0 = 0 := by
    simp [J, signedReversalUnit_apply, Fin.ext_iff, Fin.rev, show r ≠ 0 by omega]
  exact hd.trans (he.trans hz)

theorem signedNorm_projective_rep_zero (q : CFSG.PrimePower) (r : ℕ)
    (v : Fin (r + 1) → q.Extension 2) (hv : v ≠ 0) (hN : signedNorm q r v = 0) :
    signedNorm q r (Projectivization.mk (q.Extension 2) v hv).rep = 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep (q.Extension 2) v hv
  change (a : q.Extension 2) • v = (Projectivization.mk (q.Extension 2) v hv).rep at ha
  have hs := signedNorm_smul q r (a : q.Extension 2) v
  rw [hN, mul_zero] at hs
  rwa [ha] at hs

end SymmetricSubgroupAsymptotics.CFSGUnitaryHermitianPolynomial
