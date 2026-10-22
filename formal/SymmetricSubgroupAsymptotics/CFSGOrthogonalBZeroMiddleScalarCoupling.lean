import SymmetricSubgroupAsymptotics.CFSGOrthogonalBZeroMiddleProbes
import SymmetricSubgroupAsymptotics.CFSGPolarPointFunctionals
import Mathlib.Tactic.LinearCombination

/-! Fixing the actual zero-middle singular points forces ONE common
nonzero scalar on both paired projections of an image representative.
The scalars are coupled on a genuine original mixed singular plane. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBZeroMiddleScalarCoupling
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBPositiveSubspace
open CFSGOrthogonalBVectorCoordinates CFSGOrthogonalBOpposedGraphShear
open CFSGOrthogonalBZeroMiddleProbes CFSGPolarSubspacePoints CFSGSingularPlaneTriangle
open CFSGOrthogonalBIntrinsicLongRoots
variable (K : Type) [Field K] [Finite K]

abbrev Form (s : ℕ) := (gram K (s + 3)).toBilin'

theorem paired_projections_common_scalar (h2 : (2 : K) ≠ 0) (s : ℕ)
    (f : Points (Form K s) ≃ Points (Form K s))
    (horth : ∀ P Q, ZeroOn (Form K s) (f P).val (f Q).val ↔ ZeroOn (Form K s) P.val Q.val)
    (hfix : ∀ R : Points (Form K s), (∀ z ∈ R.val, z (middle (s + 3)) = 0) → f R = R)
    (P : Points (Form K s)) (v y : Index (s + 3) → K)
    (hv : v ∈ P.val) (hy : y ∈ (f P).val) (hv0 : v ≠ 0) (hy0 : y ≠ 0)
    (hvp : positivePart K (s + 3) v ≠ 0) (hvn : negativePart K (s + 3) v ≠ 0) :
    ∃ c : K, c ≠ 0 ∧
      positivePart K (s + 3) y = c • positivePart K (s + 3) v ∧
      negativePart K (s + 3) y = c • negativePart K (s + 3) v := by
  classical
  let U : Subspaces (Form K s) :=
    ⟨positiveSubspace K (s + 3), positiveSubspace_singular K (s + 3)⟩
  have hNs : ZeroOn (Form K s) (negativeSubspace K (s + 3)) (negativeSubspace K (s + 3)) := by
    rintro x ⟨a, rfl⟩ z ⟨b, rfl⟩
    simp [Form, Matrix.toBilin'_apply, gram, negativeEmbedding, Fintype.sum_sum_type]
  let W : Subspaces (Form K s) := ⟨negativeSubspace K (s + 3), hNs⟩
  have hUm (z : Index (s + 3) → K) (hz : z ∈ U.val) : z (middle (s + 3)) = 0 :=
    ((mem_positiveSubspace K (s + 3) z).mp hz).2
  have hWm (z : Index (s + 3) → K) (hz : z ∈ W.val) : z (middle (s + 3)) = 0 := by
    obtain ⟨a, rfl⟩ := hz
    rfl
  have hfixU (R : Points (Form K s)) (hR : R.val ≤ U.val) : f R = R :=
    hfix R (fun z hz => hUm z (hR hz))
  have hfixW (R : Points (Form K s)) (hR : R.val ≤ W.val) : f R = R :=
    hfix R (fun z hz => hWm z (hR hz))
  obtain ⟨a, b, ha, hb, hab, hva, hvb⟩ := exists_mixed_probes K h2 s v hvp hvn
  have hUn : restrictedPairing (Form K s) U v ≠ 0 := by
    intro hh
    have he := LinearMap.congr_fun hh ⟨a, ha⟩
    exact hva he
  have hWn : restrictedPairing (Form K s) W v ≠ 0 := by
    intro hh
    have he := LinearMap.congr_fun hh ⟨b, hb⟩
    exact hvb he
  obtain ⟨α, hα, heα⟩ := restrictedPairing_proportional (Form K s) f horth U hfixU
    P v y hv hy hv0 hy0 hUn
  obtain ⟨β, hβ, heβ⟩ := restrictedPairing_proportional (Form K s) f horth W hfixW
    P v y hv hy hv0 hy0 hWn
  let T : Subspaces (Form K s) := ⟨Submodule.span K {a, b},
    CFSGSingularPairSpan.zeroOn_pair (Form K s) a b
      (U.property a ha a ha) hab ((gram_pairing_symmetric (s + 3) b a).trans hab)
      (W.property b hb b hb)⟩
  have hTm (z : Index (s + 3) → K) (hz : z ∈ T.val) : z (middle (s + 3)) = 0 := by
    obtain ⟨r, t, rfl⟩ := Submodule.mem_span_pair.mp hz
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hUm a ha, hWm b hb, mul_zero, add_zero]
  have hfixT (R : Points (Form K s)) (hR : R.val ≤ T.val) : f R = R :=
    hfix R (fun z hz => hTm z (hR hz))
  have haT : a ∈ T.val := Submodule.subset_span (by simp)
  have hbT : b ∈ T.val := Submodule.subset_span (by simp)
  have hTn : restrictedPairing (Form K s) T v ≠ 0 := by
    intro hh
    exact hva (LinearMap.congr_fun hh ⟨a, haT⟩)
  obtain ⟨γ, hγ, heγ⟩ := restrictedPairing_proportional (Form K s) f horth T hfixT
    P v y hv hy hv0 hy0 hTn
  have hαγ : α = γ := by
    have hA := LinearMap.congr_fun heα ⟨a, ha⟩
    have hG := LinearMap.congr_fun heγ ⟨a, haT⟩
    change (Form K s) y a = α * (Form K s) v a at hA
    change (Form K s) y a = γ * (Form K s) v a at hG
    exact mul_right_cancel₀ hva (hA.symm.trans hG)
  have hβγ : β = γ := by
    have hB := LinearMap.congr_fun heβ ⟨b, hb⟩
    have hG := LinearMap.congr_fun heγ ⟨b, hbT⟩
    change (Form K s) y b = β * (Form K s) v b at hB
    change (Form K s) y b = γ * (Form K s) v b at hG
    exact mul_right_cancel₀ hvb (hB.symm.trans hG)
  have hβα : β = α := hβγ.trans hαγ.symm
  refine ⟨α, hα, ?_, ?_⟩
  · funext i
    have hh := LinearMap.congr_fun heβ ⟨Pi.single (neg (s + 3) i) 1, negative_basis_mem K _ i⟩
    change (Form K s) y (Pi.single (neg (s + 3) i) 1) =
      β * (Form K s) v (Pi.single (neg (s + 3) i) 1) at hh
    rw [pairing_negative, pairing_negative, hβα] at hh
    change y (pos (s + 3) i) = α * v (pos (s + 3) i)
    apply mul_left_cancel₀ h2
    linear_combination hh
  · funext i
    have hh := LinearMap.congr_fun heα ⟨Pi.single (pos (s + 3) i) 1, positive_basis_mem K _ i⟩
    change (Form K s) y (Pi.single (pos (s + 3) i) 1) =
      α * (Form K s) v (Pi.single (pos (s + 3) i) 1) at hh
    rw [pairing_positive, pairing_positive] at hh
    change y (neg (s + 3) i) = α * v (neg (s + 3) i)
    apply mul_left_cancel₀ h2
    linear_combination hh

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBZeroMiddleScalarCoupling
