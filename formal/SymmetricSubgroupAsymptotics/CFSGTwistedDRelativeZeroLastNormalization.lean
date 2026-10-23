import SymmetricSubgroupAsymptotics.CFSGTwistedDHyperbolicBlockLift
import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeBlockMembership
import SymmetricSubgroupAsymptotics.CFSGTwistedDZeroLastCoordinates
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSingularVectorOrbit

/-! The same smaller split-D block has literal relative-root lifts; it normalizes fixed singular vectors with vanishing final conjugate pair. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeZeroLastNormalization
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedDNaturalQuadraticTwist CFSGSerreOrdinaryTwists
open CFSGTwistedDDerivedPairedRoots CFSGTwistedA2FixedField
open CFSGTwistedDRelativeChainLift
open CFSGTwistedDZeroLastCoordinates CFSGTwistedDHyperbolicBlockLift
open CFSGTwistedDHyperbolicBlockMembership CFSGTwistedDHyperbolicBlockMatrices
open CFSGTwistedDHyperbolicBlockCoordinates CFSGOrthogonalDIndexBundledQuadratic

theorem exists_normalize (s : ℕ) (q : CFSG.PrimePower)
    (v : Index (s + 4) → q.Extension 2)
    (hv : vectorTwist (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2) v = v)
    (hp : v (Sum.inl (last (s + 2))) = 0)
    (hn : v (Sum.inr (last (s + 2))) = 0)
    (hQ : splitQuadraticForm (q.Extension 2) (s + 4) v = 0) (hv0 : v ≠ 0) :
    ∃ u : relativePreimage s q,
      (u.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v = Pi.single (Sum.inl 0) 1 := by
  let x := blockVector s q v hv
  have hx0 : x ≠ 0 := blockVector_ne_zero s q v hv hp hn hv0
  have hxQ := blockVector_splitQ_zero s q v hv hp hQ
  obtain ⟨g, hg⟩ := CFSGOrthogonalDIndexVectorCoordinates.exists_normalize_singular
    (fixedField q) (s + 1) x hx0 hxQ
  obtain ⟨u, hu⟩ := CFSGTwistedDRelativeBlockMembership.exists_relative_lift s q g
  have hb (i : Index (s + 3)) :
      ((u.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v) (blockIndex (s + 3) i) =
        (((Pi.single (Sum.inl 0) (1 : fixedField q) :
          Index (s + 3) → fixedField q) i) : q.Extension 2) := by
    rw [hu]
    have h := scalarBlockHom_action s q g.val v x
      (fun j => (blockVector_val s q v hv j).symm) i
    simpa only [hg] using h
  refine ⟨u, ?_⟩
  funext z
  obtain ⟨z, rfl⟩ := (blockEquiv (s + 3)).surjective z
  cases z with
  | inl i =>
    change ((u.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v) (blockIndex (s + 3) i) = _
    rw [hb]
    by_cases hi : i = Sum.inl 0
    · subst i
      simp [blockIndex]
    · have hne : blockIndex (s + 3) i ≠ Sum.inl 0 := by
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

end SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeZeroLastNormalization
