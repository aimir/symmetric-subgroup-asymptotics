import SymmetricSubgroupAsymptotics.CFSGHyperbolicPerpSingularWitness
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGramNondegenerate
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBParabolicColumn
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Abel

/-! Two nonorthogonal middle-normalized original singular vectors have
a middle-normalized singular common neighbour unless they are actual
antipodes. The witness is built using the original positive space and
a genuine hyperbolic pair in the actual common perpendicular. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBNonzeroMiddleCommonNeighbour
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBPositiveSubspace
open CFSGOrthogonalBIntrinsicLongRoots CFSGOrthogonalBParabolicColumn
open CFSGHyperbolicPlaneProjection
variable (K : Type) [Field K] [Finite K]

def antipode (n : ℕ) (v : Index n → K) : Index n → K :=
  (2 : K) • Pi.single (middle n) 1 - v

theorem restricted_middle_ne_zero (h2 : (2 : K) ≠ 0) (n : ℕ)
    (v w : Index n → K) (hv : (gram K n).toBilin' v v = 0)
    (hw : (gram K n).toBilin' w w = 0)
    (hvm : v (middle n) = 1) (hwm : w (middle n) = 1)
    (hc : (gram K n).toBilin' v w ≠ 0) (hanti : w ≠ antipode K n v) :
    (LinearMap.proj (middle n) : (Index n → K) →ₗ[K] K).comp
      (perp (gram K n).toBilin' v w).subtype ≠ 0 := by
  intro hl
  let B := (gram K n).toBilin'
  let m : Index n → K := Pi.single (middle n) 1
  have hs (x y : Index n → K) : B x y = B y x := gram_pairing_symmetric n x y
  have hn (x : Index n → K) (hx : ∀ y, B x y = 0) : x = 0 :=
    (gram_nondegenerate h2 n).1 x hx
  have hm (x : Index n → K) : B m x = x (middle n) := by
    rw [hs]
    exact pairing_middle K n x
  have hp : projection B v w m = 0 := by
    apply perp_nondegenerate B hs hn v w hv hw hc _ (projection_mem B hs v w hv hw hc m)
    intro x hx
    rw [hs, pairing_projection B hs v w x m hx, hs, hm]
    exact LinearMap.congr_fun hl ⟨x, hx⟩
  have heq : m = (B v w)⁻¹ • v + (B v w)⁻¹ • w := by
    rw [projection_apply] at hp
    have hvm' : B v m = 1 := (pairing_middle K n v).trans hvm
    have hwm' : B w m = 1 := (pairing_middle K n w).trans hwm
    simp only [hvm', hwm', mul_one] at hp
    exact sub_eq_zero.mp (by simpa only [sub_sub] using hp)
  have hc2 : B v w = 2 := by
    have hh := congrArg (fun x : Index n → K => x (middle n)) heq
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hvm, hwm, mul_one] at hh
    have hmm : m (middle n) = 1 := by simp [m]
    rw [hmm] at hh
    field_simp [hc] at hh
    have hh' := (eq_div_iff (show B v w ≠ 0 from hc)).mp hh
    simpa only [one_mul, one_add_one_eq_two] using hh'
  have hscl : (2 : K) * (B v w)⁻¹ = 1 := by rw [hc2, mul_inv_cancel₀ h2]
  have heq2 := congrArg (fun x : Index n → K => (2 : K) • x) heq
  simp only [smul_add, smul_smul, hscl, one_smul] at heq2
  apply hanti
  change w = (2 : K) • m - v
  rw [heq2]
  abel

theorem exists_common_neighbour (h2 : (2 : K) ≠ 0) (s : ℕ)
    (v w : Index (s + 3) → K)
    (hv : (gram K (s + 3)).toBilin' v v = 0)
    (hw : (gram K (s + 3)).toBilin' w w = 0)
    (hvm : v (middle (s + 3)) = 1) (hwm : w (middle (s + 3)) = 1)
    (hc : (gram K (s + 3)).toBilin' v w ≠ 0) (hanti : w ≠ antipode K (s + 3) v) :
    ∃ u : Index (s + 3) → K,
      (gram K (s + 3)).toBilin' u u = 0 ∧ u (middle (s + 3)) = 1 ∧
      (gram K (s + 3)).toBilin' v u = 0 ∧ (gram K (s + 3)).toBilin' w u = 0 := by
  let B := (gram K (s + 3)).toBilin'
  have hs (x y : Index (s + 3) → K) : B x y = B y x := gram_pairing_symmetric (s + 3) x y
  have hn (x : Index (s + 3) → K) (hx : ∀ y, B x y = 0) : x = 0 :=
    (gram_nondegenerate h2 (s + 3)).1 x hx
  have hP : 3 ≤ Module.finrank K (positiveSubspace K (s + 3)) := by
    rw [positiveSubspace_finrank]
    omega
  obtain ⟨x, hx, hx0, hxm⟩ :=
    CFSGHyperbolicPerpSingularWitness.exists_singular_perp_not_killed B h2 hs hn
      (positiveSubspace K (s + 3)) hP
      (fun y hy => positiveSubspace_singular K (s + 3) y hy y hy)
      v w hv hw hc (LinearMap.proj (middle (s + 3)))
      (restricted_middle_ne_zero K h2 (s + 3) v w hv hw hvm hwm hc hanti)
  refine ⟨(x (middle (s + 3)))⁻¹ • x, ?_, ?_, ?_, ?_⟩
  · change B ((x (middle (s + 3)))⁻¹ • x) ((x (middle (s + 3)))⁻¹ • x) = 0
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hx0, mul_zero]
  · change (x (middle (s + 3)))⁻¹ * x (middle (s + 3)) = 1
    exact inv_mul_cancel₀ hxm
  · change B v ((x (middle (s + 3)))⁻¹ • x) = 0
    simp only [map_smul, smul_eq_mul, show B v x = 0 from hx.1, mul_zero]
  · change B w ((x (middle (s + 3)))⁻¹ • x) = 0
    simp only [map_smul, smul_eq_mul, show B w x = 0 from hx.2, mul_zero]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBNonzeroMiddleCommonNeighbour
