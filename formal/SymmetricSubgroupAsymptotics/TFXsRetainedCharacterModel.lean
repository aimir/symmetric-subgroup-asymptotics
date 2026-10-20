import SymmetricSubgroupAsymptotics.Non2PreE7SmallAdditiveTF
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFourPairsRetainedChain

/-! The existing TF Xs projection supplies Y5's lower retained interval.
No new lower normal menu or numerical assumption is introduced. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TFXsRetainedCharacterModel
open Non2UnipotentPrefixFiniteMenu TwoFourDiagonal

private def diagonal : Xs :=
  ⟨SemidirectProduct.inl (NaturalS4.c1,NaturalS4.c1),
    inl_mem_X VW_le_Xs (by decide +kernel) (by decide +kernel)⟩

private theorem diagonal_mem : diagonal ∈ projS.ker := by
  apply MonoidHom.mem_ker.mpr
  apply Prod.ext
  · change pi0Fun NaturalS4.c1 NaturalS4.c1 = 1
    exact (pi0_ker_pair _ _ rfl).mpr ⟨by decide +kernel,rfl⟩
  · rfl

private theorem projS_ne_bot : projS.ker ≠ ⊥ := by
  intro hz
  have he : diagonal = 1 := Subgroup.mem_bot.mp (hz ▸ diagonal_mem)
  have h := congrArg (fun x : Xs => (x : W4).left.1 0) he
  change NaturalS4.c1 0 = 0 at h
  exact (by decide +kernel : NaturalS4.c1 0 ≠ 0) h

def smallAction : Xs →* Equiv.Perm (Fin 6) := LinearThree.s4c2Action.comp projS

private theorem smallAction_ker : smallAction.ker = projS.ker := by
  apply Subgroup.ext
  intro x
  change LinearThree.s4c2Action (projS x) = 1 ↔ projS x = 1
  constructor
  · intro h
    exact LinearThree.s4c2Action_injective
      (h.trans LinearThree.s4c2Action.map_one.symm)
  · intro h
    rw [h,map_one]

/-- The actual outer central quotient is the only row-specific datum.
All Xs lower-normal obligations are discharged by the existing TF proof. -/
def characterModel {U : PreE7NonPairActionClass 8}
    (q : preE7NonPairAction 8 U →* Xs) (hq : Function.Surjective q)
    (hne : q.ker ≠ ⊥)
    (cover : ∀ N : Subgroup (preE7NonPairAction 8 U),
      N.Normal → N ≠ ⊥ → q.ker ≤ N) : CertifiedFourPairCharacterModel U := by
  apply FourPairRetainedChain.characterModel q hq hne cover smallAction (by norm_num)
  · rw [smallAction_ker]
    exact projS_ne_bot
  · intro M hM hMne
    rw [smallAction_ker]
    exact projS_normal_cover M hM hMne

end SymmetricSubgroupAsymptotics.TFXsRetainedCharacterModel

end
