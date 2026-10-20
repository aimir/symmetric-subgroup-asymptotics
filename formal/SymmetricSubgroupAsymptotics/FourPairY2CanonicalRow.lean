import SymmetricSubgroupAsymptotics.FourPairY2CentralMonolith
import SymmetricSubgroupAsymptotics.FourPairY2TFImage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFourPairsRetainedChain
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTransitiveMatch

/-! The selected Y2 row at its actual canonical position.
Its six original generators are exactly retained top13, canonical entry
(8,38). Existing TF Xc covers supply the second retained interval. No new
certificate callback or classification of Y2 as a TF action is introduced. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.FourPairY2CanonicalRow
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open FourPairY2GraphPilot TwoFourDiagonal

private theorem literal_generators_checked : ∀ (j : Fin 6) (x : Fin 8),
    sourceGenerators j x = PrimitiveAffineEightFrameTop13TopCertificate.generators j x := by
  decide +kernel

/-- The selected generated source is the actual retained top13, not merely
an abstract group of the same order. -/
theorem original_eq_top13 : Original =
    Subgroup.closure (Set.range PrimitiveAffineEightFrameTop13TopCertificate.generators) := by
  have h : sourceGenerators = PrimitiveAffineEightFrameTop13TopCertificate.generators :=
    funext (fun j => Equiv.ext (literal_generators_checked j))
  change Subgroup.closure (Set.range sourceGenerators) = _
  rw [h]

private def diagonal : Xc :=
  ⟨SemidirectProduct.inl (NaturalS4.c1,NaturalS4.c1),
    inl_mem_X VW_le_Xc (by decide +kernel) (by decide +kernel)⟩

private theorem diagonal_mem : diagonal ∈ projC.ker := by
  apply MonoidHom.mem_ker.mpr
  apply Prod.ext
  · apply Subtype.ext
    change pi0Fun NaturalS4.c1 NaturalS4.c1 = 1
    exact (pi0_ker_pair _ _ rfl).mpr ⟨by decide +kernel,rfl⟩
  · rfl

private theorem projC_ne_bot : projC.ker ≠ ⊥ := by
  intro hz
  have he : diagonal = 1 := Subgroup.mem_bot.mp (hz ▸ diagonal_mem)
  have h := congrArg (fun x : Xc => (x : W4).left.1 0) he
  change NaturalS4.c1 0 = 0 at h
  exact (by decide +kernel : NaturalS4.c1 0 ≠ 0) h

private def smallAction : Xc →* Equiv.Perm (Fin 6) :=
  LinearThree.a4c2Action.comp projC

private theorem smallAction_ker : smallAction.ker = projC.ker := by
  apply Subgroup.ext
  intro x
  change LinearThree.a4c2Action (projC x) = 1 ↔ projC x = 1
  constructor
  · intro h
    exact LinearThree.a4c2Action_injective
      (h.trans LinearThree.a4c2Action.map_one.symm)
  · intro h
    rw [h, map_one]

private def centralProjection : Original →* Xc :=
  FourPairY2TFImage.imageEquiv.toMonoidHom.comp projection

private theorem centralProjection_ker : centralProjection.ker = projection.ker := by
  apply Subgroup.ext
  intro g
  change FourPairY2TFImage.imageEquiv (projection g) = 1 ↔ projection g = 1
  constructor
  · intro h
    exact FourPairY2TFImage.imageEquiv.injective
      (h.trans FourPairY2TFImage.imageEquiv.map_one.symm)
  · intro h
    rw [h, map_one]

/-- A real four-pair row constructor after exact original-action recognition.
Its only recognition datum is the group equivalence proved below from the
canonical match; all normal-axis and lower-interval facts are internal. -/
def characterModel {U : PreE7NonPairActionClass 8}
    (e : preE7NonPairAction 8 U ≃* Original) : CertifiedFourPairCharacterModel U := by
  let q := centralProjection.comp e.toMonoidHom
  have hq : Function.Surjective q :=
    FourPairY2TFImage.imageEquiv.surjective.comp (projection_surjective.comp e.surjective)
  have hfne : centralProjection.ker ≠ ⊥ := by
    rw [centralProjection_ker]
    exact FourPairY2CentralMonolith.firstStage.1
  have hfcover : ∀ N : Subgroup Original, N.Normal → N ≠ ⊥ → centralProjection.ker ≤ N := by
    intro N hN hne
    rw [centralProjection_ker]
    exact FourPairY2CentralMonolith.firstStage.2 N hN hne
  have hqne : q.ker ≠ ⊥ := by
    intro hz
    apply hfne
    apply le_antisymm _ bot_le
    intro x hx
    have hm : e.symm x ∈ q.ker := by
      change centralProjection (e (e.symm x)) = 1
      simpa only [e.apply_symm_apply] using hx
    rw [hz] at hm
    have he := congrArg e (Subgroup.mem_bot.mp hm)
    exact Subgroup.mem_bot.mpr (by simpa only [e.apply_symm_apply,e.map_one] using he)
  have hqcover : ∀ N : Subgroup (preE7NonPairAction 8 U),
      N.Normal → N ≠ ⊥ → q.ker ≤ N := by
    intro N hN hne x hx
    let M := N.map e.toMonoidHom
    have hM : M.Normal := hN.map e.toMonoidHom e.surjective
    have hMne : M ≠ ⊥ := by
      intro hz
      apply hne
      apply le_antisymm _ bot_le
      intro n hn
      have hm : e n ∈ M := ⟨n,hn,rfl⟩
      rw [hz] at hm
      exact Subgroup.mem_bot.mpr
        (e.injective ((Subgroup.mem_bot.mp hm).trans e.map_one.symm))
    obtain ⟨n,hn,he⟩ := hfcover M hM hMne (show e x ∈ centralProjection.ker from hx)
    exact e.injective he ▸ hn
  apply FourPairRetainedChain.characterModel q hq hqne hqcover smallAction (by norm_num)
  · rw [smallAction_ker]
    exact projC_ne_bot
  · intro M hM hne
    rw [smallAction_ker]
    exact projC_normal_cover M hM hne

/-- The exact original-action equivalence on the actual Y2 canonical branch.
The matching point relabelling and conjugator are retained throughout. -/
def sourceEquivOfMatch (p : PreE7PairActionClass 4)
    (M : DegreeEightCanonicalCatalogue.TransitiveLiteralMatch (preE7PairAction 4 p))
    (hindex : M.index = (12 : Fin 24)) :
    preE7PairAction 4 p ≃* Original := by
  let A := preE7PairAction 4 p
  let B := relabelSubgroup M.points A
  have hconj : relabelSubgroup M.conjugator B = Original := by
    calc
      relabelSubgroup M.conjugator B = MulAut.conj M.conjugator • B := by
        change B.map M.conjugator.permCongrHom.toMonoidHom = _
        rw [Subgroup.pointwise_smul_def]
        congr 1
      _ = (DegreeTwoPairedEightSharedTops.interface M.index).top := M.matched
      _ = Original := by
        rw [hindex]
        change Subgroup.closure
          (Set.range PrimitiveAffineEightFrameTop13TopCertificate.generators) = Original
        exact original_eq_top13.symm
  exact (BinaryPairFrame.sourceRelabelEquiv (U := A) M.points).trans
    ((BinaryPairFrame.sourceRelabelEquiv (U := B) M.conjugator).trans
      (MulEquiv.subgroupCongr hconj))

/-- The actual Y2 branch in the existing published four-pair row type.
A future exhaustive dispatcher calls this when its bare catalogue match
has index12; no target certificate callback is assumed. -/
def rowOfMatch (p : PreE7PairActionClass 4)
    (M : DegreeEightCanonicalCatalogue.TransitiveLiteralMatch (preE7PairAction 4 p))
    (hindex : M.index = (12 : Fin 24)) :
    PublishedDegreeTwoFourPairRow (preE7FourPairNonPairAction p) :=
  .character (characterModel (sourceEquivOfMatch p M hindex))

end SymmetricSubgroupAsymptotics.FourPairY2CanonicalRow

end
