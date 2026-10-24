import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSingularVectorCleanup
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOddQuadraticForm
import Mathlib.Tactic.Ring

/-! Actual negative-short and alternating-shear words clear a positive-
normalized odd-B vector at every norm. The paired negative entry retains
half the actual quadratic norm, with the original factor two explicit. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBAllNormCleanup

open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBVectorCoordinates
open CFSGOrthogonalDIndexParameters CFSGOrthogonalBOddQuadraticForm
variable (K : Type) [Field K]

def normRepresentative (s : ℕ) (c : K) : Index (s + 1) → K :=
  Sum.elim (Sum.elim (Pi.single 0 1) (Pi.single 0 ((2 : K)⁻¹ * c))) 0

theorem clear_negative_retaining_norm (h2 : (2 : K) ≠ 0) (s : ℕ)
    (v : Index (s + 1) → K) (hp : positivePart K (s + 1) v = Pi.single 0 1)
    (hm : v (middle (s + 1)) = 0) :
    ∃ g : elementaryRootGroup K (s + 1),
      (g.val : Mat K (s + 1)) *ᵥ v = normRepresentative K s (quadratic K (s + 1) v) := by
  let y := negativePart K (s + 1) v
  let z : Fin (s + 1) → K := y - Pi.single 0 (y 0)
  have hz : z 0 = 0 := by simp only [z, Pi.sub_apply, Pi.single_eq_same, sub_self]
  have hcolumn : alternating (clearNegativeParameters K s z) *ᵥ
      (Pi.single 0 1 : Fin (s + 1) → K) = -z := by
    funext j
    rw [Matrix.mulVec_single_one]
    exact clearNegative_column K s z hz j
  have hnorm : quadratic K (s + 1) v = 2 * y 0 := by
    rw [quadratic_apply, gram_norm_positive_basis K s v hp, hm,
      zero_pow (by decide : 2 ≠ 0), add_zero]
    change (2 : K)⁻¹ * (4 * y 0) = 2 * y 0
    calc
      _ = ((2 : K)⁻¹ * 2) * (2 * y 0) := by ring
      _ = _ := by rw [inv_mul_cancel₀ h2, one_mul]
  have hy0 : y 0 = (2 : K)⁻¹ * quadratic K (s + 1) v := by
    rw [hnorm, ← mul_assoc, inv_mul_cancel₀ h2, one_mul]
  refine ⟨clearNegativeElement K h2 s z, ?_⟩
  rw [clearNegativeElement_val]
  funext x
  rcases x with (i | i) | ⟨⟩
  · simpa [Matrix.fromBlocks_mulVec, pos, Function.comp_def, positivePart,
      normRepresentative] using congrFun hp i
  · simp only [Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, Matrix.one_mulVec,
      zero_add, add_zero, Sum.elim_inl, Sum.elim_inr]
    change (alternating (clearNegativeParameters K s z) *ᵥ positivePart K (s + 1) v) i +
      y i = (Pi.single 0 ((2 : K)⁻¹ * quadratic K (s + 1) v) : Fin (s + 1) → K) i
    rw [hp, hcolumn, ← hy0]
    change -(y i - (Pi.single 0 (y 0) : Fin (s + 1) → K) i) + y i = _
    ring
  · simpa [Matrix.fromBlocks_mulVec, middle, Function.comp_def,
      normRepresentative] using hm

theorem exists_normalize_positive (h2 : (2 : K) ≠ 0) (s : ℕ)
    (v : Index (s + 1) → K) (hp : positivePart K (s + 1) v = Pi.single 0 1) :
    ∃ g : elementaryRootGroup K (s + 1),
      (g.val : Mat K (s + 1)) *ᵥ v = normRepresentative K s (quadratic K (s + 1) v) := by
  let d := negativeShortElement K s 0 (v (middle (s + 1)) / 2)
  let w := (d.val : Mat K (s + 1)) *ᵥ v
  obtain ⟨hwp, hwm⟩ := negativeShort_kills_middle K h2 s v hp
  change positivePart K (s + 1) w = Pi.single 0 1 at hwp
  change w (middle (s + 1)) = 0 at hwm
  obtain ⟨c, hc⟩ := clear_negative_retaining_norm K h2 s w hwp hwm
  have hwQ : quadratic K (s + 1) w = quadratic K (s + 1) v :=
    elementary_preserves_quadratic K h2 (s + 1) d v
  rw [hwQ] at hc
  refine ⟨c * d, ?_⟩
  change ((c.val : Mat K (s + 1)) * (d.val : Mat K (s + 1))) *ᵥ v = _
  rw [← Matrix.mulVec_mulVec]
  exact hc

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBAllNormCleanup
