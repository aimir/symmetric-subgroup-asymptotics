import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSingularVectorOrbit
import Mathlib.Tactic.Ring

/-! Actual split-D elementary words normalize every nonzero vector,
retaining its quadratic norm at the paired negative coordinate. The
argument works in every characteristic, without orthogonal recognition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDAllNormVectorOrbit

open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationSLDouble
open CFSGOrthogonalDIndexVectorCoordinates CFSGOrthogonalDIndexParameters
open CFSGOrthogonalDIndexQuadraticForm CFSGOrthogonalDIndexAllRankQuadraticForm
variable (K : Type) [Field K]

/-- The fixed representative of a given norm. Its positive coordinate is one. -/
def normRepresentative (s : ℕ) (c : K) : Index (s + 2) → K :=
  Sum.elim (Pi.single 0 1) (Pi.single 0 c)

theorem clear_negative_retaining_norm (s : ℕ) (v : Index (s + 2) → K)
    (hp : positivePart K (s + 2) v = Pi.single 0 1) :
    ∃ g : elementaryRootGroup K (s + 2),
      (g.val : Mat K (s + 2)) *ᵥ v = normRepresentative K s (splitQ K v) := by
  let y := negativePart K (s + 2) v
  let z : Fin (s + 2) → K := y - Pi.single 0 (y 0)
  have hz : z 0 = 0 := by simp only [z, Pi.sub_apply, Pi.single_eq_same, sub_self]
  have hcolumn : alternating (clearNegativeParameters K s z) *ᵥ
      (Pi.single 0 1 : Fin (s + 2) → K) = -z := by
    funext j
    rw [Matrix.mulVec_single_one]
    exact clearNegative_column K s z hz j
  have hnorm : splitQ K v = y 0 := by
    change positivePart K (s + 2) v ⬝ᵥ y = y 0
    rw [hp, single_dotProduct, one_mul]
  refine ⟨clearNegativeElement K s z, ?_⟩
  change Matrix.fromBlocks (1 : Matrix (Fin (s + 2)) (Fin (s + 2)) K) 0
    (alternating (clearNegativeParameters K s z))
    (1 : Matrix (Fin (s + 2)) (Fin (s + 2)) K) *ᵥ v = _
  funext x
  cases x with
  | inl i =>
    simpa [Matrix.fromBlocks_mulVec, Function.comp_def, positivePart,
      normRepresentative] using congrFun hp i
  | inr i =>
    simp only [Matrix.fromBlocks_mulVec, Matrix.one_mulVec, Sum.elim_inr]
    change (alternating (clearNegativeParameters K s z) *ᵥ
      positivePart K (s + 2) v) i + y i =
        (Pi.single 0 (splitQ K v) : Fin (s + 2) → K) i
    rw [hp, hcolumn, hnorm]
    change -(y i - (Pi.single 0 (y 0) : Fin (s + 2) → K) i) + y i = _
    ring

/-- The SAME actual positive pivot, SL double and lower alternating shear
give a word sending any nonzero vector to its norm representative. -/
theorem exists_normalize_norm (s : ℕ) (v : Index (s + 2) → K) (hv : v ≠ 0) :
    ∃ g : elementaryRootGroup K (s + 2),
      (g.val : Mat K (s + 2)) *ᵥ v = normRepresentative K s (splitQ K v) := by
  obtain ⟨g0, hg0⟩ := exists_positive_pivot K s v hv
  let v0 := (g0.val : Mat K (s + 2)) *ᵥ v
  let j : Fin (s + 2) := ⟨1, by omega⟩
  have hj : (0 : Fin (s + 2)) ≠ j := by
    intro he
    have hh := congrArg Fin.val he
    change 0 = 1 at hh
    omega
  obtain ⟨A, hA⟩ := CFSGTypeAVectorTransitivity.exists_normalize 0 j hj
    (positivePart K (s + 2) v0) hg0
  change A.val *ᵥ positivePart K (s + 2) v0 = Pi.single 0 1 at hA
  let b := doubleIntoElementary K (s + 2) A * g0
  let w := (b.val : Mat K (s + 2)) *ᵥ v
  have hwp : positivePart K (s + 2) w = Pi.single 0 1 := by
    change positivePart K (s + 2)
      ((((doubleIntoElementary K (s + 2) A).val : Mat K (s + 2)) *
        (g0.val : Mat K (s + 2))) *ᵥ v) = _
    rw [← Matrix.mulVec_mulVec, double_positivePart]
    exact hA
  have hwnorm : splitQ K w = splitQ K v :=
    elementary_preserves_splitQ_all_ranks K (s + 2) (by omega) b v
  obtain ⟨c, hc⟩ := clear_negative_retaining_norm K s w hwp
  rw [hwnorm] at hc
  refine ⟨c * b, ?_⟩
  change ((c.val : Mat K (s + 2)) * (b.val : Mat K (s + 2))) *ᵥ v = _
  rw [← Matrix.mulVec_mulVec]
  exact hc

/-- Literal elementary transitivity on each nonzero quadratic level. -/
theorem exists_map_of_same_norm (s : ℕ) (v w : Index (s + 2) → K)
    (hv : v ≠ 0) (hw : w ≠ 0) (hQ : splitQ K v = splitQ K w) :
    ∃ g : elementaryRootGroup K (s + 2), (g.val : Mat K (s + 2)) *ᵥ v = w := by
  obtain ⟨a, ha⟩ := exists_normalize_norm K s v hv
  obtain ⟨b, hb⟩ := exists_normalize_norm K s w hw
  have hbi : (↑(b.val⁻¹) : Mat K (s + 2)) *ᵥ
      normRepresentative K s (splitQ K w) = w := by
    rw [← hb, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  refine ⟨b⁻¹ * a, ?_⟩
  change ((↑(b.val⁻¹) : Mat K (s + 2)) * (a.val : Mat K (s + 2))) *ᵥ v = w
  rw [← Matrix.mulVec_mulVec, ha, hQ, hbi]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDAllNormVectorOrbit
