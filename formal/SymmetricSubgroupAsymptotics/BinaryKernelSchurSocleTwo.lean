import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralSchurSocles
import SymmetricSubgroupAsymptotics.CubicKernelSingleTopSocleTwo

/-! An actual binary kernel separates the odd socle from its kernel.
Its exact normal image uses the quotient's all-normal bound; the binary
socle uses the existing rank-six Schur theorem. Both share two slots. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryKernelSchurSocleTwo
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem socle_two {G B : Type} [Group G] [Finite G] [IsSolvable G]
    [Group B] [Finite B] (pi : G →* B) (hpi : Function.Surjective pi)
    (hker : IsPGroup 2 pi.ker)
    (hB : ∀ (L : Subgroup B) [L.Normal], MarkedC4.normalGen L≤2)
    (hno : NoTernaryQuotient G)
    (hsection : PrimeSectionalRankBound 2 G 6)
    (hcentral : Module.finrank (ZMod 2) (Additive (binaryCentralOmega G))≤2) :
    SocleNormalGeneratorBound G 2 := by
  have hbinary := TwelvePointRemainingStructural.binarySocle_normalGen_le_two_of_noTernaryQuotient
    hno hsection hcentral
  let T := minimalNormalSoclePart G (fun M => ¬ IsPGroup 2 M)
  have he : T=minimalNormalSoclePart G
      (fun M => ¬ IsPGroup 2 M ∧ IsMulCommutative M) := by
    apply minimalNormalSoclePart_congr
    intro M hM
    exact ⟨fun h => ⟨h,minimalNormal_isMulCommutative_of_isSolvable M hM⟩,And.left⟩
  have hdis : T ⊓ pi.ker=⊥ := by
    rw [he]
    exact abelianNonPrimarySoclePart_inf_isPGroup_eq_bot 2 pi.ker hker
  letI : (T.map pi).Normal := Subgroup.Normal.map inferInstance pi hpi
  have hother : MarkedC4.normalGen T≤2 :=
    (normalGen_le_image_of_disjoint_kernel pi hpi T hdis).trans (hB (T.map pi))
  apply (socleNormalGeneratorBound_iff_normalGen_le G 2).mpr
  exact (normalGen_finiteGroupSocle_le_max_primePrimaryParts 2 G).trans
    (max_le hbinary hother)
end SymmetricSubgroupAsymptotics.BinaryKernelSchurSocleTwo
