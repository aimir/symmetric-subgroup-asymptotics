import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPositivePivot
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexClearNegativeShear
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexAllRankQuadraticForm

/-! Every original nonzero split-Q-singular D vector is normalized by
an actual original elementary word already in rank>=2. This is a
coordinate construction, with no full orthogonal orbit theorem assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexVectorCoordinates
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationSLDouble
open CFSGOrthogonalDIndexQuadraticForm CFSGOrthogonalDIndexAllRankQuadraticForm
variable (K : Type) [Field K]

theorem exists_normalize_singular (s : ℕ) (v : Index (s + 2) → K)
    (hv : v ≠ 0) (hs : splitQ K v = 0) :
    ∃ g : elementaryRootGroup K (s + 2),
      (g.val : Mat K (s + 2)) *ᵥ v = Pi.single (Sum.inl 0) 1 := by
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
  let d := doubleIntoElementary K (s + 2) A
  let b := d * g0
  let w := (b.val : Mat K (s + 2)) *ᵥ v
  have hwp : positivePart K (s + 2) w = Pi.single 0 1 := by
    change positivePart K (s + 2)
      ((((doubleIntoElementary K (s + 2) A).val : Mat K (s + 2)) *
        (g0.val : Mat K (s + 2))) *ᵥ v) = _
    rw [← Matrix.mulVec_mulVec, double_positivePart]
    exact hA
  have hws : splitQ K w = 0 :=
    (elementary_preserves_splitQ_all_ranks K (s + 2) (by omega) b v).trans hs
  obtain ⟨c, hc⟩ := exists_normalize_positive K s w hwp hws
  refine ⟨c * b, ?_⟩
  change ((c.val : Mat K (s + 2)) * (b.val : Mat K (s + 2))) *ᵥ v = _
  rw [← Matrix.mulVec_mulVec]
  exact hc

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexVectorCoordinates
