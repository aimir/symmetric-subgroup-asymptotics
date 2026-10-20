import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourTraceyNormalGenerator
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourFiveCharacterIntervalSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineBinaryExceptionalLocal
import SymmetricSubgroupAsymptotics.NormalOrderTwo
import SymmetricSubgroupAsymptotics.McIverNeumannPermutationSection
import SymmetricSubgroupAsymptotics.PermutationSocleSectionSmallThree

/-!
# Complete sharp menu for the nonzero degree-four ternary core

This module closes the nonzero-core half of the literal degree-four affine
frame.  Two published generator results are kept visible.  Tracey's refined
induced-module theorem is used in its normal-core form: a nontrivial normal
core on a faithful irreducible binary module of dimension two has one orbit
on the three nonzero dual vectors, so Corollary 4.25 gives the half-block
bound.  The sharp permutation-section socle bound is the corresponding
normal-socle consequence of the McIver--Neumann generation theorem for
subgroups of symmetric groups.  Its sole full-`S₃` exception is discharged
directly on the selected socle part.

Everything identifying the normal core, the actual top section, and every
literal retained quotient is proved here.  No finite action catalogue or
project-owned capacity hypothesis is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical commutatorElement

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

private abbrev LiteralNormalAxis4 (G : Type) [Group G] :=
  {N : Subgroup G // N.Normal}

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

theorem half_le_degreeFourSocleSlots (s : ℕ) (hs : 2 ≤ s) :
    s / 2 ≤ degreeFourSocleSlots s := by
  by_cases hsmall : s = 2 ∨ s = 3
  · rcases hsmall with rfl | rfl <;> norm_num [degreeFourSocleSlots]
  · simp only [degreeFourSocleSlots, if_neg hsmall]
    omega

/-! ## The translation-carried part -/

/-- An active translation-carried ambient minimal factor has order at least
four.  If it had order two, normality would make it central in the retained
quotient, contradicting the faithful ternary-core action. -/
theorem degreeFourTranslationMinimal_card_ge_four
    (hr : Nat.card block.Fibre = 4)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U))
    (hfaithful : DegreeFourFaithfulCoreSection block P N)
    (M : Subgroup (DegreeFourRetainedQuotient N))
    (hM : IsMinimalNormalSubgroup M)
    (hME : M ≤ degreeFourTranslationImage block P N) :
    4 ≤ Nat.card M := by
  by_contra hnot
  have hle3 : Nat.card M ≤ 3 := by omega
  obtain ⟨x, hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hM.2.1
  let y : degreeFourTranslationImage block P N := ⟨x.1, hME x.2⟩
  have hypow : (y.1 : DegreeFourRetainedQuotient N) ^ 2 = 1 :=
    congrArg Subtype.val
      (degreeFourTranslationImage_pow_two block P hr N y)
  have hxpow : x ^ 2 = 1 := by
    apply Subtype.ext
    exact hypow
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hxorder : orderOf x = 2 := orderOf_eq_prime hxpow hxne
  have hdvd : 2 ∣ Nat.card M := by
    simpa only [hxorder] using orderOf_dvd_natCard x
  obtain ⟨k, hk⟩ := hdvd
  have hcard : Nat.card M = 2 := by
    have hpos : 0 < Nat.card M := Nat.card_pos
    omega
  letI : M.Normal := hM.1
  have hcentral : M ≤ Subgroup.center (DegreeFourRetainedQuotient N) :=
    NormalOrderTwo.le_center M hcard
  have hcomm :
      ⁅degreeFourTernaryPreimageImage block P N, M⁆ = ⊥ := by
    apply le_antisymm _ bot_le
    rw [Subgroup.commutator_le]
    intro b _ m hm
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact Subgroup.mem_center_iff.mp (hcentral hm) b
  have hactive :
      ⁅degreeFourTernaryPreimageImage block P N, M⁆ = M :=
    (hfaithful M hM).2 hME
  exact hM.2.1 (hactive.symm.trans hcomm)

/-- The active translation-carried socle costs at most one generator for
each actual block. -/
theorem degreeFourTranslationSoclePart_normalGen_le_blocks
    (hr : Nat.card block.Fibre = 4)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U))
    (hfaithful : DegreeFourFaithfulCoreSection block P N) :
    MarkedC4.normalGen (degreeFourTranslationSoclePart block P N) ≤
      Nat.card block.Points := by
  exact degreeFourTranslationSoclePart_normalGen_le_of_card block P N
    4 (Nat.card block.Points) (by norm_num)
    (degreeFourTranslationMinimal_card_ge_four
      block P hr N hfaithful)
    (degreeFourTranslationImage_card_le block P hr N)

/-! ## The exact retained-top section -/

/-- Quotient of the actual block top which is retained after the literal
normal axis. -/
def degreeFourRetainedTopSectionMap
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    block.Top →*
      preE7NonPairAction w U ⧸
        (degreeFiveBlockKernelPreimage block P ⊔ N.1) :=
  (degreeFiveRetainedTopEquiv block P N).symm.toMonoidHom.comp
    (QuotientGroup.mk'
      ((degreeFiveBlockKernelPreimage block P ⊔ N.1).map
        (degreeFiveOriginalTopMap block P)))

theorem degreeFourRetainedTopSectionMap_surjective
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    Function.Surjective
      (degreeFourRetainedTopSectionMap (block := block) (P := P) N) :=
  (degreeFiveRetainedTopEquiv block P N).symm.surjective.comp
    (QuotientGroup.mk'_surjective
      ((degreeFiveBlockKernelPreimage block P ⊔ N.1).map
        (degreeFiveOriginalTopMap block P)))

/-- Any ambient normal subgroup disjoint from the retained block kernel
inherits the ordinary-generator bound from the exact quotient of the
literal transitive top. -/
theorem degreeFourRetainedBlockKernelDisjoint_normalGen_le_blocks
    (hgen : PermutationSubgroupGeneratorBound)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U))
    (H : Subgroup (DegreeFourRetainedQuotient N)) [H.Normal]
    (hdisjoint : H ⊓ degreeFiveRetainedBlockKernel block P N = ⊥) :
    MarkedC4.normalGen H ≤ Nat.card block.Points := by
  let points : block.Points ≃ Fin (Nat.card block.Points) :=
    Finite.equivFin block.Points
  let τ : block.Top →* Equiv.Perm (Fin (Nat.card block.Points)) :=
    points.permCongrHom.toMonoidHom.comp block.Top.subtype
  have hτ : Function.Injective τ :=
    points.permCongrHom.injective.comp Subtype.val_injective
  let R : Subgroup (Equiv.Perm (Fin (Nat.card block.Points))) := τ.range
  let eR : block.Top ≃* R := MulEquiv.ofBijective τ.rangeRestrict
    ⟨MonoidHom.rangeRestrict_injective_iff.mpr hτ,
      τ.rangeRestrict_surjective⟩
  let q : R →*
      preE7NonPairAction w U ⧸
        (degreeFiveBlockKernelPreimage block P ⊔ N.1) :=
    (degreeFourRetainedTopSectionMap (block := block) (P := P) N).comp
      eR.symm.toMonoidHom
  have hq : Function.Surjective q :=
    (degreeFourRetainedTopSectionMap_surjective
      (block := block) (P := P) N).comp
      eR.symm.surjective
  exact normalGen_normalSubgroup_le_degree_of_permutationSection hgen
    R q hq H (degreeFiveRestrictedRetainedTopMap block P N H)
    (degreeFiveRestrictedRetainedTopMap_injective_of_disjoint
      block P N H hdisjoint)
    (by simpa only [Fintype.card_eq_nat_card] using block.degrees_ge_two.2)

/-- A selected socle part disjoint from the retained block kernel inherits
the sharp bound from the exact quotient section of the actual block top.
At three blocks the full `S₃` exception in McIver--Neumann is discharged
by `threeBlockSelectedSoclePart_normalGen_le_one`. -/
theorem degreeFourRetainedSelectedSoclePart_normalGen_le_slots
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hs : 2 ≤ Nat.card block.Points)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U))
    (R₀ : Subgroup (DegreeFourRetainedQuotient N) → Prop)
    (hdisjoint : minimalNormalSoclePart
        (DegreeFourRetainedQuotient N) R₀ ⊓
          degreeFiveRetainedBlockKernel block P N = ⊥) :
    MarkedC4.normalGen
      (minimalNormalSoclePart (DegreeFourRetainedQuotient N) R₀) ≤
      degreeFourSocleSlots (Nat.card block.Points) := by
  by_cases hthree : Nat.card block.Points = 3
  · rw [hthree, degreeFourSocleSlots_three]
    exact threeBlockSelectedSoclePart_normalGen_le_one
      block P hthree N R₀ hdisjoint
  let H := minimalNormalSoclePart (DegreeFourRetainedQuotient N) R₀
  let points : block.Points ≃ Fin (Nat.card block.Points) :=
    Finite.equivFin block.Points
  let tau : block.Top →* Equiv.Perm (Fin (Nat.card block.Points)) :=
    points.permCongrHom.toMonoidHom.comp block.Top.subtype
  have htau : Function.Injective tau :=
    points.permCongrHom.injective.comp Subtype.val_injective
  let R : Subgroup (Equiv.Perm (Fin (Nat.card block.Points))) := tau.range
  let eR : block.Top ≃* R := MulEquiv.ofBijective tau.rangeRestrict
    ⟨MonoidHom.rangeRestrict_injective_iff.mpr htau,
      tau.rangeRestrict_surjective⟩
  let q : R →*
      preE7NonPairAction w U ⧸
        (degreeFiveBlockKernelPreimage block P ⊔ N.1) :=
    (degreeFourRetainedTopSectionMap (block := block) (P := P) N).comp
      eR.symm.toMonoidHom
  have hq : Function.Surjective q :=
    (degreeFourRetainedTopSectionMap_surjective
      (block := block) (P := P) N).comp eR.symm.surjective
  exact (normalGen_normalSubgroup_le_halfDegree_of_permutationSection
    hMN R q hq H
    (degreeFiveRestrictedRetainedTopMap block P N H)
    (degreeFiveRestrictedRetainedTopMap_injective_of_disjoint
      block P N H hdisjoint)
    (fun hs3 ↦ False.elim (hthree hs3))).trans
      (half_le_degreeFourSocleSlots (Nat.card block.Points) hs)

/-! ## Discharging the retained-core intersection by Clifford homogeneity

The published Clifford input applies to the whole literal linear block
kernel, not merely to its ternary subcore.  Nonzero `D` makes every linear
coordinate nontrivial.  The generic theorem then says that the socle part
centralized by the whole retained linear core meets that core trivially.
This is exactly the disjointness needed by the retained top-section map.
-/

/-- Nonzero `D` supplies the coordinate-nontriviality premise for the
published Clifford homogeneous-restriction theorem. -/
theorem degreeFourLinearCoordinate_range_ne_bot_of_nonzeroTernaryCore
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P ≠ ⊥)
    (i : block.Points) :
    let S := initialState hTraceyPerm block
    (CliffordHomogeneousRestriction.linearCoordinate
      S (localMap block P) i).range ≠ ⊥ := by
  let S := initialState hTraceyPerm block
  have hlocal : (degreeFourLocalBinarySign block P).ker ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card (degreeFourLocalBinarySign block P).ker = 1 := by
      rw [hbot, Subgroup.card_bot]
    rw [degreeFourLocalBinarySign_ker_card block P hr] at hcard
    omega
  obtain ⟨z, hzne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hlocal
  obtain ⟨d, hd⟩ := degreeFourTernaryCoordinate_surjective
    block P hr hD i z
  let k : CliffordHomogeneousRestriction.linearBlockKernel
      S (localMap block P) :=
    ⟨d.1, by
      simpa only [S, CliffordHomogeneousRestriction.linearBlockKernel,
        initialState, quotientEmbedding] using
          degreeFourTernaryCore_le_blockKernel block P d.2⟩
  have hk : CliffordHomogeneousRestriction.linearCoordinate
      S (localMap block P) i k ≠ 1 := by
    intro hkone
    apply hzne
    apply Subtype.ext
    calc
      (z.1 : LocalQuotient block P) =
          degreeFourTernaryCoordinate block P i d := by
            exact congrArg Subtype.val hd.symm
      _ = CliffordHomogeneousRestriction.linearCoordinate
          S (localMap block P) i k := rfl
      _ = (1 : LocalQuotient block P) := hkone
  rw [Subgroup.ne_bot_iff_exists_ne_one]
  refine ⟨⟨CliffordHomogeneousRestriction.linearCoordinate
    S (localMap block P) i k, ⟨k, rfl⟩⟩, ?_⟩
  intro h
  exact hk (congrArg Subtype.val h)

theorem degreeFourTranslationSoclePart_normalGen_le_sharp
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 4)
    (hs : 2 ≤ Nat.card block.Points)
    (hD : degreeFourTernaryCore block P ≠ ⊥)
    (i0 : block.Points)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    MarkedC4.normalGen (degreeFourTranslationSoclePart block P N) ≤
      degreeFourSocleSlots (Nat.card block.Points) :=
  degreeFourTranslationCarried_normalGen_le_sharp block P
    hTraceyPerm hr hs hD i0 N (degreeFourTranslationSoclePart block P N)
    (minimalNormalSoclePart_le_of
      (DegreeFourRetainedQuotient N)
      (fun M ↦ M ≤ degreeFourTranslationImage block P N)
      (degreeFourTranslationImage block P N)
      (fun _ _ hM ↦ hM))

/-- Complete sharp retained-socle generator menu in the nonzero-core branch.
The active binary part uses the actual normal-core cyclic-orbit bound.  The core-central
part is disjoint from the retained linear block kernel by Clifford
homogeneity and is charged through the exact actual top section. -/
noncomputable def degreeFourNonzeroRetainedSocleGeneratorBound
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 4)
    (hs : 2 ≤ Nat.card block.Points)
    (hD : degreeFourTernaryCore block P ≠ ⊥)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U))
    (hretained : ¬ E block P ≤ N.1) :
    SocleNormalGeneratorBound (DegreeFourRetainedQuotient N)
      (degreeFourSocleSlots (Nat.card block.Points)) := by
  apply (socleNormalGeneratorBound_iff_normalGen_le
    (DegreeFourRetainedQuotient N)
    (degreeFourSocleSlots (Nat.card block.Points))).2
  let S := initialState hTraceyPerm block
  let C := localTranslationChart block P
  let N' : Subgroup S.A := N.1
  letI : N'.Normal := by
    dsimp only [N']
    exact N.2
  have hirr : Representation.IsIrreducible
      (CliffordHomogeneousRestriction.localRepresentation
        S (localMap block P) (localMap_surjective block P) C).ρ := by
    rw [cliffordLocalRepresentation_rho_eq block P hTraceyPerm]
    exact binaryAffineLocalLinearRepresentation_irreducible block P
  have hfaith : Function.Injective
      (CliffordHomogeneousRestriction.localRepresentation
        S (localMap block P) (localMap_surjective block P) C).ρ := by
    rw [cliffordLocalRepresentation_rho_eq block P hTraceyPerm]
    exact binaryAffineLocalLinearRepresentation_injective block P
  have hcoord : ∀ i : block.Points,
      (CliffordHomogeneousRestriction.linearCoordinate
        S (localMap block P) i).range ≠ ⊥ := by
    intro i
    exact degreeFourLinearCoordinate_range_ne_bot_of_nonzeroTernaryCore
      block P hTraceyPerm hr hD i
  have hretained' : ¬ CliffordHomogeneousRestriction.elementaryKernel
      S (localMap block P) ≤ N' := by
    simpa only [N', S, C,
      CliffordHomogeneousRestriction.elementaryKernel,
      ActualWreathAffineCapacity.K, initialState] using hretained
  have hmax :=
    hClifford.normalGen_socle_le_max_retainedElementary_coreCentral
      S (localMap block P) (localMap_surjective block P) C
      hirr hfaith hcoord N' hretained'
  refine hmax.trans (max_le ?_ ?_)
  · change MarkedC4.normalGen
      (minimalNormalSoclePart (DegreeFourRetainedQuotient N)
        (fun M ↦ M ≤ degreeFourTranslationImage block P N)) ≤
          degreeFourSocleSlots (Nat.card block.Points)
    let i0 : block.Points := Classical.choice inferInstance
    exact degreeFourTranslationSoclePart_normalGen_le_sharp
      block P hTraceyPerm hr hs hD i0 N
  · let H := trivialActionSoclePart
      (DegreeFourRetainedQuotient N)
      (CliffordHomogeneousRestriction.retainedCoreImage
        S (localMap block P) N')
    letI : H.Normal := by
      dsimp only [H]
      infer_instance
    have hdisjoint : H ⊓ degreeFiveRetainedBlockKernel block P N = ⊥ := by
      simpa only [H, N', S,
        degreeFiveRetainedBlockKernel, degreeFiveBlockKernelPreimage,
        CliffordHomogeneousRestriction.retainedCoreImage,
        CliffordHomogeneousRestriction.corePreimage,
        CliffordHomogeneousRestriction.linearBlockKernel,
        initialState, quotientEmbedding] using
          hClifford.trivialActionSoclePart_inf_retainedCore_eq_bot
            S (localMap block P) (localMap_surjective block P) C
            hirr hfaith hcoord N' hretained'
    apply degreeFourRetainedSelectedSoclePart_normalGen_le_slots
      block P hMN hs N
      (fun M ↦ ¬ ⁅CliffordHomogeneousRestriction.retainedCoreImage
        S (localMap block P) N', M⁆ = M)
    exact hdisjoint

/-- Final nonzero-core degree-four source.  Every literal normal axis not
containing the translation intersection has the sharp complete character
menu, so the finite-band wrapper applies unconditionally. -/
noncomputable def degreeFourNonzeroCharacterIntervalSource
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 4)
    (hs : 2 ≤ Nat.card block.Points)
    (hsUpper : Nat.card block.Points ≤ 3072)
    (hD : degreeFourTernaryCore block P ≠ ⊥) :
    PreE7RankTailSourceOrYonedaTopData w U :=
  degreeFourCharacterIntervalSource block P hZmud lit family
    (fun N hretained ↦
      degreeFourNonzeroRetainedSocleGeneratorBound
        block P hMN hClifford hTraceyPerm
          hr hs hD N hretained)
    hr hs hsUpper

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
