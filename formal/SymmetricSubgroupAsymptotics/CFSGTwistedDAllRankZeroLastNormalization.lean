import SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankBlockAction
import SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankZeroLastCoordinates
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSingularVectorOrbit

/-! The actual retained smaller split-D block normalizes every nonzero
fixed singular vector with zero final pair, including rank three. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankZeroLastNormalization
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedDNaturalQuadraticTwist CFSGSerreOrdinaryTwists
open CFSGTwistedDRelativeElementaryGroup CFSGTwistedA2FixedField
open CFSGTwistedDAllRankZeroLastCoordinates CFSGTwistedDAllRankBlockAction
open CFSGTwistedDAllRankBlockMembership CFSGTwistedDHyperbolicBlockMatrices
open CFSGTwistedDHyperbolicBlockCoordinates CFSGOrthogonalDIndexBundledQuadratic

theorem exists_normalize (n : ℕ) (q : CFSG.PrimePower)
    (v : Index (n + 3) → q.Extension 2)
    (hv : vectorTwist (q.Extension 2) (n + 1) (definingFieldAutomorphism q 2) v = v)
    (hp : v (Sum.inl (last (n + 1))) = 0)
    (hn : v (Sum.inr (last (n + 1))) = 0)
    (hQ : splitQuadraticForm (q.Extension 2) (n + 3) v = 0) (hv0 : v ≠ 0) :
    ∃ u : relativeRootGroup (n + 1) q,
      (u.val : Mat (q.Extension 2) (n + 3)) *ᵥ v = Pi.single (Sum.inl 0) 1 := by
  let x := blockVector n q v hv
  have hx0 : x ≠ 0 := blockVector_ne_zero n q v hv hp hn hv0
  have hxQ := blockVector_splitQ_zero n q v hv hp hQ
  obtain ⟨g, hg⟩ := CFSGOrthogonalDIndexVectorCoordinates.exists_normalize_singular
    (fixedField q) n x hx0 hxQ
  let u := blockRelativeHom n q g
  have hu : u.val = scalarBlockHom n q g.val := rfl
  have hb (i : Index (n + 2)) :
      ((u.val : Mat (q.Extension 2) (n + 3)) *ᵥ v) (blockIndex (n + 2) i) =
        (((Pi.single (Sum.inl 0) (1 : fixedField q) :
          Index (n + 2) → fixedField q) i) : q.Extension 2) := by
    rw [hu]
    have h := scalarBlockHom_action n q g.val v x
      (fun j => (blockVector_val n q v hv j).symm) i
    simpa only [hg] using h
  refine ⟨u, ?_⟩
  funext z
  obtain ⟨z, rfl⟩ := (blockEquiv (n + 2)).surjective z
  cases z with
  | inl i =>
    change ((u.val : Mat (q.Extension 2) (n + 3)) *ᵥ v) (blockIndex (n + 2) i) = _
    rw [hb]
    by_cases hi : i = Sum.inl 0
    · subst i
      simp [blockIndex]
    · have hne : blockIndex (n + 2) i ≠ Sum.inl 0 := by
        intro h
        apply hi
        apply blockIndex_injective (n + 2)
        exact h
      simp [hi, hne]
  | inr j =>
    fin_cases j
    · change ((u.val : Mat (q.Extension 2) (n + 3)) *ᵥ v)
        (blockEquiv (n + 2) (Sum.inr (0 : Fin 2))) = _
      rw [blockEquiv_zero, hu, scalarBlockHom_val, blockMatrixHom_positive_last]
      change v (Sum.inl (last (n + 1))) = _
      rw [hp]
      simp [Pi.single_apply, Fin.ext_iff]
    · change ((u.val : Mat (q.Extension 2) (n + 3)) *ᵥ v)
        (blockEquiv (n + 2) (Sum.inr (1 : Fin 2))) = _
      rw [blockEquiv_one, hu, scalarBlockHom_val, blockMatrixHom_negative_last]
      change v (Sum.inr (last (n + 1))) = _
      rw [hn]
      simp [Pi.single_apply]

end SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankZeroLastNormalization
