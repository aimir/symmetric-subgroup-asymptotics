import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryPairedTorus
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCentralRadical

/-! Actual first-line stabilizers scale the extreme central root by the
field norm of their first-column scalar. The signed form equation, not a
named unitary-group identification, supplies the inverse last row. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGSerreOrdinaryTwists CFSGTwistedAUnitaryNaturalRadical
open CFSGTwistedAUnitaryUpperArrays

theorem signedReversal_first_row {K : Type} [Field K] (r : ℕ) (j : Fin (r + 1)) :
    (signedReversalUnit K r : Mat K r) 0 j = if j = Fin.last r then 1 else 0 := by
  have h0 : (0 : Fin (r + 1)).rev = Fin.last r := by
    apply Fin.ext
    simp [Fin.rev]
  simp only [signedReversalUnit_apply, h0, signWeight, Fin.val_zero, pow_zero]
  simp only [eq_comm]

theorem isometric_inverse_last_row {K : Type} [Field K] (r : ℕ)
    (sigma : K ≃+* K) (g : (Mat K r)ˣ) (a : K)
    (hform : ((g : Mat K r).map sigma).transpose *
      (signedReversalUnit K r : Mat K r) * (g : Mat K r) = (signedReversalUnit K r : Mat K r))
    (hcol : ∀ i, (g : Mat K r) i 0 = if i = 0 then a else 0) (j : Fin (r + 1)) :
    ((g⁻¹ : (Mat K r)ˣ) : Mat K r) (Fin.last r) j = sigma a * (if j = Fin.last r then 1 else 0) := by
  have hright : ((g : Mat K r).map sigma).transpose * (signedReversalUnit K r : Mat K r) =
      (signedReversalUnit K r : Mat K r) * ((g⁻¹ : (Mat K r)ˣ) : Mat K r) := by
    calc
      _ = (((g : Mat K r).map sigma).transpose *
          (signedReversalUnit K r : Mat K r) * (g : Mat K r)) * ((g⁻¹ : (Mat K r)ˣ) : Mat K r) := by
        rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := congrArg (fun M : Mat K r => M * ((g⁻¹ : (Mat K r)ˣ) : Mat K r)) hform
  have hj := congrArg (fun M : Mat K r => M 0 j) hright
  change (((g : Mat K r).map sigma).transpose * (signedReversalUnit K r : Mat K r)) 0 j =
    ((signedReversalUnit K r : Mat K r) * ((g⁻¹ : (Mat K r)ˣ) : Mat K r)) 0 j at hj
  simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, hcol,
    signedReversal_first_row, apply_ite] using hj.symm

theorem extreme_single_conjugation {K : Type} [Field K] (r : ℕ)
    (sigma : K ≃+* K) (g : (Mat K r)ˣ) (a b : K)
    (hform : ((g : Mat K r).map sigma).transpose *
      (signedReversalUnit K r : Mat K r) * (g : Mat K r) = (signedReversalUnit K r : Mat K r))
    (hcol : ∀ i, (g : Mat K r) i 0 = if i = 0 then a else 0) :
    (g : Mat K r) * (1 + Matrix.single (0 : Fin (r + 1)) (Fin.last r) b) * ((g⁻¹ : (Mat K r)ˣ) : Mat K r) =
      1 + Matrix.single (0 : Fin (r + 1)) (Fin.last r) (a * sigma a * b) := by
  have hfirst : (g : Mat K r) * Matrix.single (0 : Fin (r + 1)) (Fin.last r) b =
      Matrix.single (0 : Fin (r + 1)) (Fin.last r) (a * b) := by
    ext i j
    by_cases hj : j = Fin.last r
    · subst j
      rw [Matrix.mul_single_apply_same]
      rw [hcol]
      by_cases hi : i = 0 <;> simp [hi, eq_comm]
    · rw [Matrix.mul_single_apply_of_ne b (0 : Fin (r + 1)) (Fin.last r) i j hj]
      simp [Ne.symm hj]
  have hlast : Matrix.single (0 : Fin (r + 1)) (Fin.last r) (a * b) * ((g⁻¹ : (Mat K r)ˣ) : Mat K r) =
      Matrix.single (0 : Fin (r + 1)) (Fin.last r) (a * sigma a * b) := by
    ext i j
    by_cases hi : i = 0
    · subst i
      rw [Matrix.single_mul_apply_same, isometric_inverse_last_row r sigma g a hform hcol]
      by_cases hj : j = Fin.last r <;> simp [hj, eq_comm] <;> ring
    · rw [Matrix.single_mul_apply_of_ne (a * b) (0 : Fin (r + 1)) (Fin.last r) i j hi]
      simp [Ne.symm hi]
  rw [mul_add, mul_one, add_mul, Units.mul_inv, hfirst]
  exact congrArg (fun M : Mat K r => 1 + M) hlast

theorem centralParameter_norm_mul_condition (q : CFSG.PrimePower) (s : ℕ)
    (a b : q.Extension 2) (hb : Condition q s 0 b) :
    Condition q s 0 (a * definingFieldAutomorphism q 2 a * b) := by
  apply (centralCondition_iff q s _).mpr
  have hs := (centralCondition_iff q s b).mp hb
  have htwice : definingFieldAutomorphism q 2 (definingFieldAutomorphism q 2 a) = a :=
    extension_two_pow_twice q a
  change definingFieldAutomorphism q 2 (a * definingFieldAutomorphism q 2 a * b) +
    parity q s * (a * definingFieldAutomorphism q 2 a * b) = 0
  rw [map_mul, map_mul, htwice]
  calc
    _ = (a * definingFieldAutomorphism q 2 a) *
      (definingFieldAutomorphism q 2 b + parity q s * b) := by ring
    _ = 0 := by rw [hs, mul_zero]

theorem pairedTorus_centralFixed_conjugation (q : CFSG.PrimePower) (s : ℕ)
    (a b : q.Extension 2) (ha : a ≠ 0) (hb : Condition q (s + 1) 0 b) :
    pairedTorus q s a * centralFixed q (s + 1) b hb * (pairedTorus q s a)⁻¹ =
      centralFixed q (s + 1) (a * definingFieldAutomorphism q 2 a * b)
        (centralParameter_norm_mul_condition q (s + 1) a b hb) := by
  let g := pairedTorus q s a
  have haxis := pairedTorus_first_axis q s a 1 ha
  rw [mul_one] at haxis
  have hcol (i : Fin (s + 4)) : (g.val.val : Mat (q.Extension 2) (s + 3)) i 0 =
      if i = 0 then a else 0 := by
    have hi := congrArg (fun v : Fin (s + 4) → q.Extension 2 => v i) haxis
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply, eq_comm] using hi
  have hform := fixed_unit_signedForm (q.Extension 2) (s + 3)
    (definingFieldAutomorphism q 2).toRingHom g.val.val g.property
  change ((g.val.val : Mat (q.Extension 2) (s + 3)).map
    (definingFieldAutomorphism q 2)).transpose *
    (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3)) *
    (g.val.val : Mat (q.Extension 2) (s + 3)) = _ at hform
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  change (g.val.val : Mat (q.Extension 2) (s + 3)) *
    ((centralFixed q (s + 1) b hb).val.val : Mat (q.Extension 2) (s + 3)) *
    (((g.val.val)⁻¹ : (Mat (q.Extension 2) (s + 3))ˣ) : Mat (q.Extension 2) (s + 3)) =
      ((centralFixed q (s + 1) (a * definingFieldAutomorphism q 2 a * b)
        (centralParameter_norm_mul_condition q (s + 1) a b hb)).val.val : Mat (q.Extension 2) (s + 3))
  rw [show ((centralFixed q (s + 1) b hb).val.val : Mat (q.Extension 2) (s + 3)) =
    1 + Matrix.single (0 : Fin (s + 4)) (Fin.last (s + 3)) b from radicalCentral_matrix q (s + 1) b hb]
  rw [show ((centralFixed q (s + 1) (a * definingFieldAutomorphism q 2 a * b)
    (centralParameter_norm_mul_condition q (s + 1) a b hb)).val.val :
      Mat (q.Extension 2) (s + 3)) =
    1 + Matrix.single (0 : Fin (s + 4)) (Fin.last (s + 3)) (a * definingFieldAutomorphism q 2 a * b) from
      radicalCentral_matrix q (s + 1) (a * definingFieldAutomorphism q 2 a * b)
        (centralParameter_norm_mul_condition q (s + 1) a b hb)]
  exact extreme_single_conjugation (s + 3) (definingFieldAutomorphism q 2) g.val.val a b hform hcol

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
