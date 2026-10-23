import SymmetricSubgroupAsymptotics.CFSGOrthogonalDTailCrossingSpace
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootComponents
import SymmetricSubgroupAsymptotics.CFSGTwistedDResidualPlane
import SymmetricSubgroupAsymptotics.CFSGTwistedDResidualDiagonal

/-! The antidiagonal final-plane residue crosses exactly one positive
coordinate. Actual elementary D matrices have even crossing distance,
so this residue is excluded also in characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDResidualComponent
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexTailCoordinates
open CFSGOrthogonalDIndexPositiveSpace CFSGOrthogonalDIndexPositiveGraph
open CFSGOrthogonalDIsometryIndexCrossingSpaces CFSGOrthogonalDTailCrossingSpace
open CFSGTwistedDFrameReduction CFSGOrthogonalDGenerationForkTorus
open CFSGOrthogonalDCoordinateDiagonal CFSGTwistedDResidualPlane
open CFSGTwistedDNormOneUnits CFSGTwistedDNaturalFieldTwist CFSGSerreOrdinaryTwists
open CFSGOrthogonalDIndexQuadraticForm

theorem residual_antidiagonal_crossing (K : Type) [Field K] (n : ℕ) (b : (Mat K 1)ˣ)
    (h00 : (b : Mat K 1) (Sum.inl 0) (Sum.inl 0) = 0) :
    (positiveSpace K (n + 2)).map
      (ambientLinearEquiv K (n + 2) (residualEmbedding K n b)).toLinearMap =
        crossingSpace K (n + 2) (last n) := by
  have hbase (v : Index 1 → K) (hv : v ∈ positiveSpace K 1) :
      (b : Mat K 1) *ᵥ v ∈ crossingSpace K 1 0 := by
    constructor
    · change (∑ i : Index 1, (b : Mat K 1) (Sum.inl 0) i * v i) = 0
      simp [Fintype.sum_sum_type, h00, hv 0]
    · intro i hi
      have he : i = 0 := Subsingleton.elim _ _
      exact (hi he).elim
  have hm (v : Index (n + 2) → K) (hv : v ∈ positiveSpace K (n + 2)) :
      (residualEmbedding K n b : Mat K (n + 2)) *ᵥ v ∈
        crossingSpace K (n + 2) (last n) := by
    induction n with
    | zero =>
      exact tail_maps_positive_to_crossing K 1 0 (b : Mat K 1) hbase v hv
    | succ n ih =>
      exact tail_maps_positive_to_crossing K (n + 2) (last n)
        (residualEmbedding K n b : Mat K (n + 2)) ih v hv
  have hle : (positiveSpace K (n + 2)).map
      (ambientLinearEquiv K (n + 2) (residualEmbedding K n b)).toLinearMap ≤
        crossingSpace K (n + 2) (last n) := by
    rintro x ⟨v, hv, rfl⟩
    exact hm v hv
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [LinearEquiv.finrank_map_eq, positiveSpace_finrank, crossingSpace_finrank]

theorem elementary_residual_not_antidiagonal (K : Type) [Field K] (s : ℕ)
    (b : (Mat K 1)ˣ)
    (he : residualEmbedding K (s + 2) b ∈ elementaryRootGroup K (s + 4)) :
    (b : Mat K 1) (Sum.inl 0) (Sum.inl 0) ≠ 0 := by
  intro h00
  let g : elementaryRootGroup K (s + 4) := ⟨residualEmbedding K (s + 2) b, he⟩
  have hd := CFSGOrthogonalDIndexRootComponents.elementary_even_distance K s g
  change Even (CFSGOrthogonalDIndexSingularComponents.distance (s + 4)
    (positiveSpace K (s + 4)) ((positiveSpace K (s + 4)).map
      (ambientLinearEquiv K (s + 4) (residualEmbedding K (s + 2) b)).toLinearMap)) at hd
  rw [residual_antidiagonal_crossing K (s + 2) b h00, crossing_distance_one] at hd
  norm_num at hd

theorem exists_residual_diagonal (s : ℕ) (q : CFSG.PrimePower)
    (b : quadraticPreserving (q.Extension 2) 1)
    (ht : unitTwist (q.Extension 2) 0 (definingFieldAutomorphism q 2)
      (tailUnitHom (q.Extension 2) 1 b.val) = tailUnitHom (q.Extension 2) 1 b.val)
    (he : residualEmbedding (q.Extension 2) (s + 2) b.val ∈
      elementaryRootGroup (q.Extension 2) (s + 4)) :
    ∃ c : normOneUnits q, b.val = pairDiagonalHom (q.Extension 2) 1 0 c.val := by
  obtain ⟨c, hc | hc⟩ := exists_normOne_form q b ht
  · refine ⟨c, ?_⟩
    apply Units.ext
    rw [pairDiagonalHom_val]
    ext x y
    rcases x with x | x <;> rcases y with y | y <;>
      fin_cases x <;> fin_cases y <;>
      simp [Matrix.diagonal_apply, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2]
  · exact (elementary_residual_not_antidiagonal (q.Extension 2) s b.val he hc.1).elim

end SymmetricSubgroupAsymptotics.CFSGTwistedDResidualComponent
