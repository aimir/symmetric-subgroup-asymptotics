import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOpposedCommonRatio
import SymmetricSubgroupAsymptotics.CFSGPolarPointFunctionals
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBMiddleNormDichotomy

/-! Fixing the points of both original opposed coordinate spaces
forces two actual nonzero paired projection scalars. No fixation of
mixed points and no equality between these scalars is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBOpposedProjectionScalars
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBPositiveSubspace
open CFSGOrthogonalBVectorCoordinates CFSGOrthogonalBOpposedGraphShear
open CFSGOrthogonalBOpposedCommonRatio CFSGOrthogonalBZeroMiddleProbes
open CFSGPolarSubspacePoints CFSGSingularPlaneTriangle
variable (K : Type) [Field K] [Finite K]

theorem paired_projection_scalars (h2 : (2 : K) ≠ 0) (s : ℕ)
    (f : Points (gram K (s + 3)).toBilin' ≃ Points (gram K (s + 3)).toBilin')
    (horth : ∀ P Q, ZeroOn (gram K (s + 3)).toBilin' (f P).val (f Q).val ↔
      ZeroOn (gram K (s + 3)).toBilin' P.val Q.val)
    (hfixP : ∀ R : Points (gram K (s + 3)).toBilin',
      R.val ≤ positiveSubspace K (s + 3) → f R = R)
    (hfixZ : ∀ R : Points (gram K (s + 3)).toBilin',
      R.val ≤ negativeSubspace K (s + 3) → f R = R)
    (P : Points (gram K (s + 3)).toBilin') (v y : Index (s + 3) → K)
    (hv : v ∈ P.val) (hy : y ∈ (f P).val) (hv0 : v ≠ 0) (hy0 : y ≠ 0)
    (hvp : positivePart K (s + 3) v ≠ 0) (hvn : negativePart K (s + 3) v ≠ 0) :
    ∃ a b : K, a ≠ 0 ∧ b ≠ 0 ∧
      positivePart K (s + 3) y = b • positivePart K (s + 3) v ∧
      negativePart K (s + 3) y = a • negativePart K (s + 3) v := by
  let B := (gram K (s + 3)).toBilin'
  let U : Subspaces B := ⟨positiveSubspace K (s + 3), positiveSubspace_singular K (s + 3)⟩
  let W := negativeSingular K (s + 3)
  obtain ⟨p, q, hp, hq, _, hvp', hvq⟩ := exists_mixed_probes K h2 s v hvp hvn
  have hUn : restrictedPairing B U v ≠ 0 := by
    intro hh
    exact hvp' (LinearMap.congr_fun hh ⟨p, hp⟩)
  have hWn : restrictedPairing B W v ≠ 0 := by
    intro hh
    exact hvq (LinearMap.congr_fun hh ⟨q, hq⟩)
  obtain ⟨a, ha, hea⟩ := restrictedPairing_proportional B f horth U hfixP
    P v y hv hy hv0 hy0 hUn
  obtain ⟨b, hb, heb⟩ := restrictedPairing_proportional B f horth W hfixZ
    P v y hv hy hv0 hy0 hWn
  refine ⟨a, b, ha, hb, ?_, ?_⟩
  · funext i
    have hh := LinearMap.congr_fun heb ⟨Pi.single (neg (s + 3) i) 1, negative_basis_mem K _ i⟩
    change B y (Pi.single (neg (s + 3) i) 1) = b * B v (Pi.single (neg (s + 3) i) 1) at hh
    rw [pairing_negative, pairing_negative] at hh
    change y (pos (s + 3) i) = b * v (pos (s + 3) i)
    apply mul_left_cancel₀ h2
    linear_combination hh
  · funext i
    have hh := LinearMap.congr_fun hea ⟨Pi.single (pos (s + 3) i) 1, positive_basis_mem K _ i⟩
    change B y (Pi.single (pos (s + 3) i) 1) = a * B v (Pi.single (pos (s + 3) i) 1) at hh
    rw [pairing_positive, pairing_positive] at hh
    change y (neg (s + 3) i) = a * v (neg (s + 3) i)
    apply mul_left_cancel₀ h2
    linear_combination hh

omit [Finite K] in
theorem pairing_positive_subspace (n : ℕ) (v y : Index n → K) (a : K)
    (hn : negativePart K n y = a • negativePart K n v)
    (p : Index n → K) (hp : p ∈ positiveSubspace K n) :
    (gram K n).toBilin' y p = a * (gram K n).toBilin' v p := by
  obtain ⟨x, rfl⟩ := hp
  rw [gram_pairing_coordinates, gram_pairing_coordinates]
  change (∑ i : Fin n, (y (pos n i) * 2 * 0 + y (neg n i) * 2 * x i)) +
      y (middle n) * 0 =
    a * ((∑ i : Fin n, (v (pos n i) * 2 * 0 + v (neg n i) * 2 * x i)) + v (middle n) * 0)
  simp only [mul_zero, zero_add, add_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he := congrFun hn i
  change y (neg n i) = a * v (neg n i) at he
  rw [he]
  ring

omit [Finite K] in
theorem pairing_negative_subspace (n : ℕ) (v y : Index n → K) (b : K)
    (hp : positivePart K n y = b • positivePart K n v)
    (q : Index n → K) (hq : q ∈ negativeSubspace K n) :
    (gram K n).toBilin' y q = b * (gram K n).toBilin' v q := by
  obtain ⟨x, rfl⟩ := hq
  rw [gram_pairing_coordinates, gram_pairing_coordinates]
  change (∑ i : Fin n, (y (pos n i) * 2 * x i + y (neg n i) * 2 * 0)) +
      y (middle n) * 0 =
    b * ((∑ i : Fin n, (v (pos n i) * 2 * x i + v (neg n i) * 2 * 0)) + v (middle n) * 0)
  simp only [mul_zero, add_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he := congrFun hp i
  change y (pos n i) = b * v (pos n i) at he
  rw [he]
  ring

omit [Finite K] in
theorem norm_of_paired_scalars (n : ℕ) (v y : Index n → K)
    (hv : (gram K n).toBilin' v v = 0) (hy : (gram K n).toBilin' y y = 0)
    (hvm : v (middle n) = 1) (a b : K)
    (hp : positivePart K n y = b • positivePart K n v)
    (hn : negativePart K n y = a • negativePart K n v) :
    y (middle n) ^ 2 = a * b := by
  have hd : CFSGParabolicQuadricCount.dotDual (fun i => 4 * positivePart K n y i)
      (negativePart K n y) = a * b *
        CFSGParabolicQuadricCount.dotDual (fun i => 4 * positivePart K n v i)
          (negativePart K n v) := by
    rw [hp, hn]
    change (∑ i : Fin n, 4 * (b * positivePart K n v i) * (a * negativePart K n v i)) =
      (a * b) * ∑ i : Fin n, 4 * positivePart K n v i * negativePart K n v i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [CFSGOrthogonalBSingularVectorCount.gram_norm_dot, hvm, one_pow] at hv
  rw [CFSGOrthogonalBSingularVectorCount.gram_norm_dot, hd] at hy
  linear_combination hy - (a * b) * hv

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBOpposedProjectionScalars
