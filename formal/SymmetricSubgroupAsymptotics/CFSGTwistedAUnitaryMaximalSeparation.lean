import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOppositeProjection
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRootAxisPairing
import SymmetricSubgroupAsymptotics.CFSGHermitianMaximalClosure
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Every literal unitary isotropic subspace is the intersection of its
maximal isotropic extensions. A separating functional is represented by
an actual opposite-half singular vector, then the checked normalization
words transport the separation to an arbitrary subspace. All ranks and
characteristics are retained; no polar-space classification is an input. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUnitaryParameters CFSGSerreOrdinaryTwists
open CFSGHermitianOrthogonalSpan

theorem unitary_standard_subspace_separated (q : CFSG.PrimePower) (r : ℕ)
    (S : Submodule (q.Extension 2) (Fin (r + 1) → q.Extension 2))
    (hSE : S ≤ unitaryStandardSingularSpace q r) :
    SeparatedByMaximal (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) S := by
  intro x hx
  by_cases hxE : x ∈ unitaryStandardSingularSpace q r
  · have hn : ¬∀ f : Module.Dual (q.Extension 2) (Fin (r + 1) → q.Extension 2),
        f ∈ S.dualAnnihilator → f x = 0 := by
      intro hall
      exact hx ((Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff S x).mp hall)
    push Not at hn
    obtain ⟨f, hfS, hfx⟩ := hn
    obtain ⟨y, hy, hpair⟩ := exists_unitaryOpposite_dual q r f
    have hyS (z : Fin (r + 1) → q.Extension 2) (hz : z ∈ S) :
        unitaryNaturalPair q r y z = 0 :=
      (hpair z (hSE hz)).trans ((S.mem_dualAnnihilator f).mp hfS z hz)
    have hSy (z : Fin (r + 1) → q.Extension 2) (hz : z ∈ S) :
        unitaryNaturalPair q r z y = 0 := (unitaryNaturalPair_zero_swap q r z y).mpr (hyS z hz)
    apply exists_maximalIsotropic_excluding_of_witness (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) S
      (fun z hz w hw => unitaryStandardSingularSpace_pair_zero q r z (hSE hz) w (hSE hw)) x y
      hy hSy hyS
    change unitaryNaturalPair q r y x ≠ 0
    rwa [hpair x hxE]
  · exact ⟨unitaryStandardSingularSpace q r, unitaryStandardSingularSpace_maximal q r, hSE, hxE⟩

theorem unitary_isotropic_separated_by_maximal (q : CFSG.PrimePower) (r : ℕ)
    (S : Submodule (q.Extension 2) (Fin (r + 1) → q.Extension 2))
    (hS : Orthogonal (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) S S) :
    SeparatedByMaximal (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) S := by
  obtain ⟨g, hg⟩ := exists_unitary_subspace_normalization q r S hS
  let e := unitaryNaturalLinearEquiv q r g
  let T := unitarySubspaceImage q r g S
  have hTE : T ≤ unitaryStandardSingularSpace q r := by
    rintro _ ⟨z, hz, rfl⟩
    exact hg z hz
  intro x hx
  have hex : e x ∉ T := by
    rintro ⟨z, hz, he⟩
    exact hx (e.injective he ▸ hz)
  obtain ⟨M, hM, hTM, hxM⟩ := unitary_standard_subspace_separated q r T hTE (e x) hex
  let N := M.comap e.toLinearMap
  have hSN : S ≤ N := by
    intro z hz
    exact hTM ⟨z, hz, rfl⟩
  have hNN : Orthogonal (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) N N := by
    intro z hz w hw
    exact (unitaryNaturalLinearEquiv_pair q r g z w).symm.trans (hM.1 (e z) hz (e w) hw)
  have hNmax : MaximalIsotropic (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) N := by
    refine ⟨hNN, ?_⟩
    intro U hU hNU
    have hMle : M ≤ unitarySubspaceImage q r g U := by
      intro z hz
      have hez : e.symm z ∈ N := by
        change e (e.symm z) ∈ M
        simpa only [LinearEquiv.apply_symm_apply] using hz
      exact ⟨e.symm z, hNU hez, e.apply_symm_apply z⟩
    have heq := hM.2 (unitarySubspaceImage q r g U) (unitarySubspaceImage_pair_zero q r g U hU) hMle
    apply le_antisymm
    · intro z hz
      change e z ∈ M
      rw [← heq]
      exact ⟨z, hz, rfl⟩
    · exact hNU
  exact ⟨N, hNmax, hSN, hxM⟩

theorem unitary_isotropic_maximalPointClosure (q : CFSG.PrimePower) (r : ℕ)
    (S : Submodule (q.Extension 2) (Fin (r + 1) → q.Extension 2))
    (hS : Orthogonal (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) S S) :
    maximalPointClosure (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r)
      (pointSet (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) S) =
      pointSet (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) S :=
  maximalPointClosure_pointSet_eq _ _ S (unitary_isotropic_separated_by_maximal q r S hS)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
