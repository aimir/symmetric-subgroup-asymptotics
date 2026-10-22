import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOpposedProjectionScalars
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBNegativeDilation

/-! The actual uniform zero-middle ratio is necessarily a nonzero
square. One original middle-one singular vector and one original mixed
probe line force the scalar relation; its image norm supplies the square.
No image-middle hypothesis, onto assumption for representatives, or
square-class recognition premise is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBDilationRatioSquare
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBPositiveSubspace
open CFSGOrthogonalBVectorCoordinates CFSGOrthogonalBOpposedGraphShear
open CFSGOrthogonalBOpposedCommonRatio CFSGOrthogonalBZeroMiddleProbes
open CFSGOrthogonalBOpposedProjectionScalars CFSGOrthogonalBMiddleNormDichotomy
open CFSGOrthogonalBIntrinsicLongRoots CFSGPolarSubspacePoints CFSGSingularPlaneTriangle
variable (K : Type) [Field K] [Finite K]

omit [Finite K] in
theorem dilation_positive (n : ℕ) (t : K) (p : Index n → K)
    (hp : p ∈ positiveSubspace K n) : CFSGOrthogonalBNegativeDilation.map K n t p = p := by
  obtain ⟨x, rfl⟩ := hp
  funext i
  rcases i with (i | i) | ⟨⟩ <;>
    simp [CFSGOrthogonalBNegativeDilation.map, positiveEmbedding]

omit [Finite K] in
theorem dilation_negative (n : ℕ) (t : K) (q : Index n → K)
    (hq : q ∈ negativeSubspace K n) : CFSGOrthogonalBNegativeDilation.map K n t q = t • q := by
  obtain ⟨x, rfl⟩ := hq
  funext i
  rcases i with (i | i) | ⟨⟩ <;>
    simp [CFSGOrthogonalBNegativeDilation.map, negativeEmbedding]

theorem ratio_square_of_middle_one (h2 : (2 : K) ≠ 0) (s : ℕ)
    (f : Points (gram K (s + 3)).toBilin' ≃ Points (gram K (s + 3)).toBilin')
    (horth : ∀ P Q, ZeroOn (gram K (s + 3)).toBilin' (f P).val (f Q).val ↔
      ZeroOn (gram K (s + 3)).toBilin' P.val Q.val)
    (hfixP : ∀ R : Points (gram K (s + 3)).toBilin',
      R.val ≤ positiveSubspace K (s + 3) → f R = R)
    (hfixZ : ∀ R : Points (gram K (s + 3)).toBilin',
      R.val ≤ negativeSubspace K (s + 3) → f R = R)
    (t : K) (ht : t ≠ 0)
    (hratio : ∀ (z : Index (s + 3) → K) (hz0 : z ≠ 0)
      (hz : (gram K (s + 3)).toBilin' z z = 0), z (middle (s + 3)) = 0 →
        (f (ray (gram K (s + 3)).toBilin' z hz0 hz)).val =
          Submodule.span K {CFSGOrthogonalBNegativeDilation.map K (s + 3) t z})
    (v : Index (s + 3) → K) (hv : (gram K (s + 3)).toBilin' v v = 0)
    (hvm : v (middle (s + 3)) = 1) : ∃ u : K, u ≠ 0 ∧ u ^ 2 = t := by
  let B := (gram K (s + 3)).toBilin'
  have hv0 : v ≠ 0 := by
    intro hz
    have he := congrFun hz (middle (s + 3))
    exact one_ne_zero (hvm.symm.trans he)
  let P := ray B v hv0 hv
  have hvP : v ∈ P.val := Submodule.subset_span (by simp)
  obtain ⟨w, hw, hw0⟩ := point_nonzero B (f P)
  have hwn : B w w = 0 := (f P).property.2 w hw w hw
  obtain ⟨a, b, ha, hb, hpos, hneg⟩ := paired_projection_scalars K h2 s f horth hfixP hfixZ
    P v w hvP hw hv0 hw0 (projections_ne_zero K _ v hv hvm).1
      (projections_ne_zero K _ v hv hvm).2
  obtain ⟨p, q, hp, hq, hpq, hA, hC⟩ := exists_mixed_probes K h2 s v
    (projections_ne_zero K _ v hv hvm).1 (projections_ne_zero K _ v hv hvm).2
  let d := B v p / B v q
  let z := p - d • q
  have hz0 : z ≠ 0 := by
    intro hz
    change p - d • q = 0 at hz
    have he : p = d • q := sub_eq_zero.mp hz
    have hpZ : p ∈ negativeSubspace K (s + 3) := by
      rw [he]
      exact (negativeSubspace K _).smul_mem d hq
    have hp0 : p = 0 := (disjoint_iff_inf_le.mp (positive_negative_disjoint K (s + 3))) ⟨hp, hpZ⟩
    apply hA
    rw [hp0, map_zero]
  have hpp : B p p = 0 := positiveSubspace_singular K _ p hp p hp
  have hqq : B q q = 0 := (negativeSingular K _).property q hq q hq
  have hpqB : B p q = 0 := hpq
  have hqp : B q p = 0 := (gram_pairing_symmetric _ q p).trans hpq
  have hzn : B z z = 0 := by
    change B (p - d • q) (p - d • q) = 0
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, hpp, hqq, hpqB, hqp, mul_zero, sub_zero]
  have hpm : p (middle (s + 3)) = 0 := ((mem_positiveSubspace K _ p).mp hp).2
  have hqm : q (middle (s + 3)) = 0 := by
    obtain ⟨x, rfl⟩ := hq
    rfl
  have hzm : z (middle (s + 3)) = 0 := by
    change p (middle (s + 3)) - d * q (middle (s + 3)) = 0
    rw [hpm, hqm, mul_zero, sub_zero]
  have hvz : B v z = 0 := by
    change B v (p - d • q) = 0
    rw [map_sub, map_smul, smul_eq_mul]
    change B v p - (B v p / B v q) * B v q = 0
    rw [div_mul_cancel₀ _ hC, sub_self]
  let Q := ray B z hz0 hzn
  have hzQ : z ∈ Q.val := Submodule.subset_span (by simp)
  have hPQ : ZeroOn B P.val Q.val :=
    (zeroOn_iff_representatives B P Q v z hvP hzQ hv0 hz0).mpr hvz
  have hDz : CFSGOrthogonalBNegativeDilation.map K (s + 3) t z = p - (t * d) • q := by
    change CFSGOrthogonalBNegativeDilation.map K (s + 3) t (p - d • q) = _
    rw [map_sub, map_smul, dilation_positive K _ t p hp, dilation_negative K _ t q hq,
      smul_smul, mul_comm d t]
  have hDzQ : CFSGOrthogonalBNegativeDilation.map K (s + 3) t z ∈ (f Q).val := by
    rw [hratio z hz0 hzn hzm]
    exact Submodule.subset_span (by simp)
  have hwDz := ((horth P Q).mpr hPQ) w hw _ hDzQ
  have hwp : B w p = a * B v p := pairing_positive_subspace K _ v w a hneg p hp
  have hwq : B w q = b * B v q := pairing_negative_subspace K _ v w b hpos q hq
  change B w (CFSGOrthogonalBNegativeDilation.map K (s + 3) t z) = 0 at hwDz
  rw [hDz, map_sub, map_smul, smul_eq_mul, hwp, hwq] at hwDz
  have he : (t * d) * (b * B v q) = t * b * B v p := by
    change (t * (B v p / B v q)) * (b * B v q) = _
    calc
      _ = (t * b) * ((B v p / B v q) * B v q) := by ring
      _ = t * b * B v p := by rw [div_mul_cancel₀ _ hC]
  rw [he] at hwDz
  have hab : a = t * b := by
    have heq : (a - t * b) * B v p = 0 := by linear_combination hwDz
    exact sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_right hA)
  have hnorm := norm_of_paired_scalars K _ v w hv hwn hvm a b hpos hneg
  have hnorm' : w (middle (s + 3)) ^ 2 = t * b ^ 2 := hnorm.trans (by rw [hab]; ring)
  have hwm : w (middle (s + 3)) ≠ 0 := by
    intro hz
    have he := hnorm'
    rw [hz, zero_pow (by decide : (2 : ℕ) ≠ 0)] at he
    exact (mul_ne_zero ht (pow_ne_zero 2 hb)) he.symm
  refine ⟨w (middle (s + 3)) / b, div_ne_zero hwm hb, ?_⟩
  rw [div_pow]
  exact (div_eq_iff (pow_ne_zero 2 hb)).mpr hnorm'

omit [Finite K] in
theorem exists_middle_one_singular (h2 : (2 : K) ≠ 0) (s : ℕ) :
    ∃ v : Index (s + 3) → K, (gram K (s + 3)).toBilin' v v = 0 ∧
      v (middle (s + 3)) = 1 := by
  classical
  have h4 : (4 : K) ≠ 0 := by
    have h := pow_ne_zero 2 h2
    norm_num at h ⊢
    exact h
  let v : Index (s + 3) → K := Sum.elim
    (Sum.elim (Pi.single (0 : Fin (s + 3)) 1) (Pi.single (0 : Fin (s + 3)) (-(4 : K)⁻¹)))
    (fun _ => 1)
  refine ⟨v, ?_, rfl⟩
  rw [CFSGOrthogonalBSingularVectorCount.gram_norm_dot]
  change (∑ i : Fin (s + 3), ((4 : K) *
    (Pi.single (0 : Fin (s + 3)) (1 : K) : Fin (s + 3) → K) i *
    (Pi.single (0 : Fin (s + 3)) (-(4 : K)⁻¹) : Fin (s + 3) → K) i)) + 1 ^ 2 = 0
  simp [Pi.single_apply, mul_ite, ite_mul, mul_neg, h4]

theorem ratio_is_nonzero_square (h2 : (2 : K) ≠ 0) (s : ℕ)
    (f : Points (gram K (s + 3)).toBilin' ≃ Points (gram K (s + 3)).toBilin')
    (horth : ∀ P Q, ZeroOn (gram K (s + 3)).toBilin' (f P).val (f Q).val ↔
      ZeroOn (gram K (s + 3)).toBilin' P.val Q.val)
    (hfixP : ∀ R : Points (gram K (s + 3)).toBilin',
      R.val ≤ positiveSubspace K (s + 3) → f R = R)
    (hfixZ : ∀ R : Points (gram K (s + 3)).toBilin',
      R.val ≤ negativeSubspace K (s + 3) → f R = R)
    (t : K) (ht : t ≠ 0)
    (hratio : ∀ (z : Index (s + 3) → K) (hz0 : z ≠ 0)
      (hz : (gram K (s + 3)).toBilin' z z = 0), z (middle (s + 3)) = 0 →
        (f (ray (gram K (s + 3)).toBilin' z hz0 hz)).val =
          Submodule.span K {CFSGOrthogonalBNegativeDilation.map K (s + 3) t z}) :
    ∃ u : K, u ≠ 0 ∧ u ^ 2 = t := by
  obtain ⟨v, hv, hvm⟩ := exists_middle_one_singular K h2 s
  exact ratio_square_of_middle_one K h2 s f horth hfixP hfixZ t ht hratio v hv hvm

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBDilationRatioSquare
