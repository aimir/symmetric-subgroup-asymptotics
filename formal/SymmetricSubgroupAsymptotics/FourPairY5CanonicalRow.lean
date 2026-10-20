import SymmetricSubgroupAsymptotics.FourPairY5TFImage
import SymmetricSubgroupAsymptotics.FourPairY345CanonicalMatches
import SymmetricSubgroupAsymptotics.TFXsRetainedCharacterModel

/-! Actual canonical Y5 branch. The first central kernel is proved inside
its original eight-point source; the lower group is the existing TF Xs.
All original normals, including the first central kernel itself, are retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FourPairY5CanonicalRow
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open FourPairY5CentralGraph TwoFourDiagonal

private theorem original_generators_checked : ∀ (j : Fin 6) (x : Fin 8),
    sourceGenerators j x = PrimitiveAffineEightFrameTop17TopCertificate.generators j x := by
  decide +kernel

theorem original_eq_source : Original = FourPairY345CentralFrames.source 2 := by
  have h : sourceGenerators = PrimitiveAffineEightFrameTop17TopCertificate.generators :=
    funext (fun j => Equiv.ext (original_generators_checked j))
  change Subgroup.closure (Set.range sourceGenerators) = _
  rw [h]
  rfl

def sourceEquiv : Original ≃* FourPairY345CentralFrames.source 2 :=
  MulEquiv.subgroupCongr original_eq_source

def centralElement : Original :=
  sourceEquiv.symm (FourPairY345CentralFrames.constantKernel 2)

private theorem central_points_checked : ∀ x : Fin 8,
    FourPairY345CentralFrames.constantPermutation 2 x = centralFlip x := by
  decide +kernel

theorem centralElement_val : (centralElement : Equiv.Perm (Fin 8)) = centralFlip := by
  change ((FourPairY345CentralFrames.constantKernel 2 :
    FourPairY345CentralFrames.source 2) : Equiv.Perm (Fin 8)) = centralFlip
  exact Equiv.ext central_points_checked

private theorem central_ne_one_checked : centralFlip (0 : Fin 8) ≠ 0 := by
  decide +kernel

theorem central_mem_normal (N : Subgroup Original) (hN : N.Normal) (hne : N ≠ ⊥) :
    centralElement ∈ N := by
  let M := N.map sourceEquiv.toMonoidHom
  have hM : M.Normal := hN.map sourceEquiv.toMonoidHom sourceEquiv.surjective
  have hMne : M ≠ ⊥ := by
    intro hz
    apply hne
    apply le_antisymm _ bot_le
    intro n hn
    have hm : sourceEquiv n ∈ M := ⟨n,hn,rfl⟩
    rw [hz] at hm
    exact Subgroup.mem_bot.mpr
      (sourceEquiv.injective ((Subgroup.mem_bot.mp hm).trans sourceEquiv.map_one.symm))
  obtain ⟨n,hn,he⟩ :=
    FourPairY345CentralFrames.constant_mem_every_nontrivial_normal 2 M hM hMne
  have he' : n = centralElement := by
    apply sourceEquiv.injective
    exact he.trans (sourceEquiv.apply_symm_apply _).symm
  exact he' ▸ hn

theorem firstStage : projection.ker ≠ ⊥ ∧
    ∀ N : Subgroup Original, N.Normal → N ≠ ⊥ → projection.ker ≤ N := by
  have hc : centralElement ∈ projection.ker :=
    (kernel_mem_iff centralElement).mpr (Or.inr centralElement_val)
  constructor
  · intro hz
    have he := congrArg (fun g : Original => (g : Equiv.Perm (Fin 8)) 0)
      (Subgroup.mem_bot.mp (hz ▸ hc))
    change (centralElement : Equiv.Perm (Fin 8)) 0 = 0 at he
    rw [centralElement_val] at he
    exact central_ne_one_checked he
  · intro N hN hne x hx
    rcases (kernel_mem_iff x).mp hx with h | h
    · exact h.symm ▸ N.one_mem
    · have he : x = centralElement := Subtype.ext (h.trans centralElement_val.symm)
      exact he.symm ▸ central_mem_normal N hN hne

private def centralProjection : Original →* Xs :=
  FourPairY5TFImage.imageEquiv.toMonoidHom.comp projection

private theorem centralProjection_ker : centralProjection.ker = projection.ker := by
  apply Subgroup.ext
  intro g
  change FourPairY5TFImage.imageEquiv (projection g) = 1 ↔ projection g = 1
  constructor
  · intro h
    exact FourPairY5TFImage.imageEquiv.injective
      (h.trans FourPairY5TFImage.imageEquiv.map_one.symm)
  · intro h
    rw [h,map_one]

def characterModel {U : PreE7NonPairActionClass 8}
    (e : preE7NonPairAction 8 U ≃* Original) : CertifiedFourPairCharacterModel U := by
  let q := centralProjection.comp e.toMonoidHom
  have hq : Function.Surjective q :=
    FourPairY5TFImage.imageEquiv.surjective.comp (projection_surjective.comp e.surjective)
  have hfne : centralProjection.ker ≠ ⊥ := by
    rw [centralProjection_ker]
    exact firstStage.1
  have hfcover : ∀ N : Subgroup Original, N.Normal → N ≠ ⊥ → centralProjection.ker ≤ N := by
    intro N hN hne
    rw [centralProjection_ker]
    exact firstStage.2 N hN hne
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
  exact TFXsRetainedCharacterModel.characterModel q hq hqne hqcover

/-- Real branch at canonical index 16; no certificate-valued callback. -/
def rowOfMatch (p : PreE7PairActionClass 4)
    (M : DegreeEightCanonicalCatalogue.TransitiveLiteralMatch (preE7PairAction 4 p))
    (hindex : M.index = (16 : Fin 24)) :
    PublishedDegreeTwoFourPairRow (preE7FourPairNonPairAction p) :=
  .character (characterModel
    ((FourPairY345CanonicalMatches.sourceEquivOfMatch 2 p M hindex).trans sourceEquiv.symm))

end SymmetricSubgroupAsymptotics.FourPairY5CanonicalRow
end
