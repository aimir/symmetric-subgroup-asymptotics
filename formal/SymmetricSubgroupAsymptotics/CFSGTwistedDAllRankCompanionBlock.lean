import SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankAxisTransport
import SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankZeroLastCoordinates
import SymmetricSubgroupAsymptotics.CFSGSplitQuadraticPoleRootWords

/-! Actual relative-root words normalize zero-terminal-pair companions,
fixing the first positive axis, in every relative rank at least three. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankCompanionBlock
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedDNaturalQuadraticTwist CFSGSerreOrdinaryTwists
open CFSGTwistedDRelativeElementaryGroup CFSGTwistedA2FixedField
open CFSGTwistedDAllRankZeroLastCoordinates CFSGTwistedDAllRankBlockAction
open CFSGTwistedDAllRankBlockMembership CFSGTwistedDHyperbolicBlockMatrices
open CFSGTwistedDHyperbolicBlockCoordinates CFSGOrthogonalDIndexBundledQuadratic

theorem exists_normalize_fix_first (n : ℕ) (q : CFSG.PrimePower)
    (v : Index (n + 3) → q.Extension 2)
    (hv : vectorTwist (q.Extension 2) (n + 1) (definingFieldAutomorphism q 2) v = v)
    (hp : v (Sum.inl (last (n + 1))) = 0)
    (hn : v (Sum.inr (last (n + 1))) = 0)
    (hQ : splitQuadraticForm (q.Extension 2) (n + 3) v = 0)
    (hy : v (Sum.inr 0) = 1) :
    ∃ u : relativeRootGroup (n + 1) q,
      (u.val : Mat (q.Extension 2) (n + 3)) *ᵥ Pi.single (Sum.inl 0) 1 =
        Pi.single (Sum.inl 0) 1 ∧
      (u.val : Mat (q.Extension 2) (n + 3)) *ᵥ v = Pi.single (Sum.inr 0) 1 := by
  let x := blockVector n q v hv
  have hxy : x (Sum.inr 0) = 1 := by
    apply Subtype.ext
    exact hy
  have hxQ := blockVector_splitQ_zero n q v hv hp hQ
  obtain ⟨g, hgaxis, hg⟩ := CFSGSplitQuadraticPoleRootWords.exists_normalize_companion
    (fixedField q) (n + 1) (by omega) x hxy hxQ
  let u := blockRelativeHom n q g
  have hu : u.val = scalarBlockHom n q g.val := rfl
  have hb (i : Index (n + 2)) :
      ((u.val : Mat (q.Extension 2) (n + 3)) *ᵥ v) (blockIndex (n + 2) i) =
        (((Pi.single (Sum.inr 0) (1 : fixedField q) :
          Index (n + 2) → fixedField q) i) : q.Extension 2) := by
    rw [hu]
    have h := scalarBlockHom_action n q g.val v x
      (fun j => (blockVector_val n q v hv j).symm) i
    simpa only [hg] using h
  refine ⟨u, ?_, ?_⟩
  · rw [hu]
    exact CFSGTwistedDAllRankAxisTransport.scalarBlock_basis_action n q g.val
      (Sum.inl 0) (Sum.inl 0) hgaxis
  funext z
  obtain ⟨z, rfl⟩ := (blockEquiv (n + 2)).surjective z
  cases z with
  | inl i =>
    change ((u.val : Mat (q.Extension 2) (n + 3)) *ᵥ v) (blockIndex (n + 2) i) = _
    rw [hb]
    by_cases hi : i = Sum.inr 0
    · subst i
      simp [blockIndex]
    · have hne : blockIndex (n + 2) i ≠ Sum.inr 0 := by
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

end SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankCompanionBlock
