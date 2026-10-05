import SymmetricSubgroupAsymptotics.CliffordHomogeneousRestrictionInput
import SymmetricSubgroupAsymptotics.NormalGeneratorTypeSharing

/-!
# Sharing socle generators across a whole linear block kernel

The affine exceptional rows do not need a prime-local subcore of the
linear block kernel.  Clifford homogeneity already separates the ambient
socle into the factors carried by the retained elementary kernel and the
factors centralized by the whole retained linear kernel.  These two action
types share normal-generator slots by the intrinsic Goursat theorem.

This file states that argument for an arbitrary actual-wreath elementary
chart.  Degree-specific files only have to prove that every literal linear
coordinate is nontrivial and bound the two resulting socle parts.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace CliffordHomogeneousRestriction

/-- Every nontrivial normal subgroup of a finite group contains an ambient
minimal normal subgroup.  This finite-poset form is kept here because the
whole-kernel sharing argument is deliberately independent of every
degree-specific affine file. -/
private theorem exists_minimalNormal_le_normal_of_ne_bot
    {G : Type} [Group G] [Finite G]
    (K : Subgroup G) [K.Normal] (hK : K ≠ ⊥) :
    ∃ M : Subgroup G, IsMinimalNormalSubgroup M ∧ M ≤ K := by
  let good : Subgroup G → Prop := fun M => M.Normal ∧ M ≠ ⊥
  obtain ⟨M, hMK, hminimal⟩ :=
    Finite.exists_le_minimal (p := good) (a := K)
      (show good K from ⟨inferInstance, hK⟩)
  refine ⟨M, ⟨hminimal.1.1, hminimal.1.2, ?_⟩, hMK⟩
  intro L hLnormal hLne hLM
  exact hminimal.eq_of_le ⟨hLnormal, hLne⟩ hLM

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
  [MulAction Q I] [FaithfulSMul Q I]
  (S : ActualWreathCompressionState Q I)
  {D' : Type} [Group D'] [Finite D']
  (phi : S.D →* D') (hphi : Function.Surjective phi)
  (C : ElementaryMinimalNormalChart phi.ker)

/-- The action-active socle part is exactly the ambient socle part carried
by the retained elementary kernel.  This is the reusable form of the
faithful-core-section conclusion. -/
theorem Input.nontrivialActionSoclePart_eq_retainedElementary
    (input : Input)
    (hirreducible : Representation.IsIrreducible
      (localRepresentation S phi hphi C).ρ)
    (hlocalFaithful : Function.Injective
      (localRepresentation S phi hphi C).ρ)
    (hcoordinate : ∀ i : I, (linearCoordinate S phi i).range ≠ ⊥)
    (N : Subgroup S.A) [N.Normal]
    (hretained : ¬ elementaryKernel S phi ≤ N) :
    nontrivialActionSoclePart (S.A ⧸ N) (retainedCoreImage S phi N) =
      minimalNormalSoclePart (S.A ⧸ N)
        (fun M => M ≤ retainedElementaryImage S phi N) := by
  apply minimalNormalSoclePart_congr
  intro M hM
  exact input.commutator_eq_iff_minimalNormal_le_retainedElementary
    S phi hphi C hirreducible hlocalFaithful hcoordinate N hretained M hM

/-- The core-central socle part meets the whole retained linear core
trivially.  A nonzero intersection would contain an ambient minimal normal
factor; Clifford then puts that factor in the elementary image, where the
retained core acts fully, contradicting centrality. -/
theorem Input.trivialActionSoclePart_inf_retainedCore_eq_bot
    (input : Input)
    (hirreducible : Representation.IsIrreducible
      (localRepresentation S phi hphi C).ρ)
    (hlocalFaithful : Function.Injective
      (localRepresentation S phi hphi C).ρ)
    (hcoordinate : ∀ i : I, (linearCoordinate S phi i).range ≠ ⊥)
    (N : Subgroup S.A) [N.Normal]
    (hretained : ¬ elementaryKernel S phi ≤ N) :
    trivialActionSoclePart (S.A ⧸ N) (retainedCoreImage S phi N) ⊓
        retainedCoreImage S phi N = ⊥ := by
  by_contra hne
  obtain ⟨M, hM, hMK⟩ := exists_minimalNormal_le_normal_of_ne_bot
    (trivialActionSoclePart (S.A ⧸ N) (retainedCoreImage S phi N) ⊓
      retainedCoreImage S phi N) hne
  have hMD : M ≤ retainedCoreImage S phi N := hMK.trans inf_le_right
  have hME : M ≤ retainedElementaryImage S phi N :=
    (input.minimalNormal_le_retainedCore_iff_le_retainedElementary
      S phi hphi C hirreducible hlocalFaithful hcoordinate N hretained
        M hM).mp hMD
  have hfull : ⁅retainedCoreImage S phi N, M⁆ = M :=
    (input.commutator_eq_iff_minimalNormal_le_retainedElementary
      S phi hphi C hirreducible hlocalFaithful hcoordinate N hretained
        M hM).mpr hME
  have hcentralM : M ≤ Subgroup.centralizer
      (retainedCoreImage S phi N : Set (S.A ⧸ N)) :=
    (hMK.trans inf_le_left).trans
      (trivialActionSoclePart_le_centralizer
        (S.A ⧸ N) (retainedCoreImage S phi N))
  have hbot : ⁅retainedCoreImage S phi N, M⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcentralM
  exact hM.2.1 (hfull.symm.trans hbot)

/-- Reusable whole-kernel max sharing.  Once the active elementary part and
the core-central part are bounded, the whole ambient socle costs the maximum
of their two normal-generator budgets. -/
theorem Input.normalGen_socle_le_max_retainedElementary_coreCentral
    (input : Input)
    (hirreducible : Representation.IsIrreducible
      (localRepresentation S phi hphi C).ρ)
    (hlocalFaithful : Function.Injective
      (localRepresentation S phi hphi C).ρ)
    (hcoordinate : ∀ i : I, (linearCoordinate S phi i).range ≠ ⊥)
    (N : Subgroup S.A) [N.Normal]
    (hretained : ¬ elementaryKernel S phi ≤ N) :
    MarkedC4.normalGen (finiteGroupSocle (S.A ⧸ N)) ≤
      max
        (MarkedC4.normalGen
          (minimalNormalSoclePart (S.A ⧸ N)
            (fun M => M ≤ retainedElementaryImage S phi N)))
        (MarkedC4.normalGen
          (trivialActionSoclePart (S.A ⧸ N)
            (retainedCoreImage S phi N))) := by
  have hmax := normalGen_finiteGroupSocle_le_max_actionSocleParts
    (S.A ⧸ N) (retainedCoreImage S phi N)
  rw [input.nontrivialActionSoclePart_eq_retainedElementary
    S phi hphi C hirreducible hlocalFaithful hcoordinate N hretained] at hmax
  exact hmax

end CliffordHomogeneousRestriction
end SymmetricSubgroupAsymptotics

end
