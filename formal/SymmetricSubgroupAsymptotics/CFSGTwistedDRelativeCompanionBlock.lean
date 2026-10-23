import SymmetricSubgroupAsymptotics.CFSGTwistedDHyperbolicBlockLift
import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeBlockMembership
import SymmetricSubgroupAsymptotics.CFSGTwistedDZeroLastCoordinates
import SymmetricSubgroupAsymptotics.CFSGSplitQuadraticPoleRootWords
import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeAxisTransport

/-! Literal relative-root words fixing the positive first pole normalize
a singular companion once its final conjugate coordinates are zero. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeCompanionBlock
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedDNaturalQuadraticTwist CFSGSerreOrdinaryTwists
open CFSGTwistedDDerivedPairedRoots CFSGTwistedA2FixedField
open CFSGTwistedDRelativeChainLift
open CFSGTwistedDZeroLastCoordinates CFSGTwistedDHyperbolicBlockLift
open CFSGTwistedDHyperbolicBlockMembership CFSGTwistedDHyperbolicBlockMatrices
open CFSGTwistedDHyperbolicBlockCoordinates CFSGOrthogonalDIndexBundledQuadratic

theorem exists_normalize_fix_first (s : ℕ) (q : CFSG.PrimePower)
    (v : Index (s + 4) → q.Extension 2)
    (hv : vectorTwist (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2) v = v)
    (hp : v (Sum.inl (last (s + 2))) = 0)
    (hn : v (Sum.inr (last (s + 2))) = 0)
    (hQ : splitQuadraticForm (q.Extension 2) (s + 4) v = 0)
    (hy : v (Sum.inr 0) = 1) :
    ∃ u : relativePreimage s q,
      (u.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ Pi.single (Sum.inl 0) 1 =
        Pi.single (Sum.inl 0) 1 ∧
      (u.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v = Pi.single (Sum.inr 0) 1 := by
  let x := blockVector s q v hv
  have hxy : x (Sum.inr 0) = 1 := by
    apply Subtype.ext
    exact hy
  have hxQ := blockVector_splitQ_zero s q v hv hp hQ
  obtain ⟨g, hgaxis, hg⟩ := CFSGSplitQuadraticPoleRootWords.exists_normalize_companion
    (fixedField q) (s + 2) (by omega) x hxy hxQ
  obtain ⟨u, hu⟩ := CFSGTwistedDRelativeBlockMembership.exists_relative_lift s q g
  have hb (i : Index (s + 3)) :
      ((u.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v) (blockIndex (s + 3) i) =
        (((Pi.single (Sum.inr 0) (1 : fixedField q) :
          Index (s + 3) → fixedField q) i) : q.Extension 2) := by
    rw [hu]
    have h := scalarBlockHom_action s q g.val v x
      (fun j => (blockVector_val s q v hv j).symm) i
    simpa only [hg] using h
  refine ⟨u, ?_, ?_⟩
  · rw [hu]
    exact CFSGTwistedDRelativeAxisTransport.scalarBlock_basis_action s q g.val
      (Sum.inl 0) (Sum.inl 0) hgaxis
  funext z
  obtain ⟨z, rfl⟩ := (blockEquiv (s + 3)).surjective z
  cases z with
  | inl i =>
    change ((u.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v) (blockIndex (s + 3) i) = _
    rw [hb]
    by_cases hi : i = Sum.inr 0
    · subst i
      simp [blockIndex]
    · have hne : blockIndex (s + 3) i ≠ Sum.inr 0 := by
        intro h
        apply hi
        apply blockIndex_injective (s + 3)
        exact h
      simp [hi, hne]
  | inr j =>
    fin_cases j
    · change ((u.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v)
        (blockEquiv (s + 3) (Sum.inr (0 : Fin 2))) = _
      rw [blockEquiv_zero, hu, scalarBlockHom_val, blockMatrixHom_positive_last]
      change v (Sum.inl (last (s + 2))) = _
      rw [hp]
      simp [Pi.single_apply, Fin.ext_iff]
    · change ((u.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v)
        (blockEquiv (s + 3) (Sum.inr (1 : Fin 2))) = _
      rw [blockEquiv_one, hu, scalarBlockHom_val, blockMatrixHom_negative_last]
      change v (Sum.inr (last (s + 2))) = _
      rw [hn]
      simp [Pi.single_apply]

end SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeCompanionBlock
