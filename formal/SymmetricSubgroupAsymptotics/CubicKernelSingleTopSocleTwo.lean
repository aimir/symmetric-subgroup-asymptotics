import SymmetricSubgroupAsymptotics.NormalGeneratorActualIntersectionImage
import SymmetricSubgroupAsymptotics.OriginalKernelElementaryChart
import SymmetricSubgroupAsymptotics.NonPrimeAbelianSoclePart
import SymmetricSubgroupAsymptotics.BinaryBySymmetricThree
import SymmetricSubgroupAsymptotics.SocleNormalSubgroupGeneratorInheritance
import SymmetricSubgroupAsymptotics.NormalGeneratorDisjointKernelImage
import SymmetricSubgroupAsymptotics.SocleActionPartQuotientKernel

/-! A cyclic ternary kernel module and a single cubic factor in the
actual linear top share two whole-socle positions. The non-3 row injects
into the actual top; the 3 row uses one kernel and one image position. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CubicKernelSingleTopSocleTwo
open OriginalKernelModuleChart
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem socle_two {G B : Type} [Group G] [Finite G] [IsSolvable G]
    [Group B] [Finite B] (pi : G →* B) (hpi : Function.Surjective pi)
    (A : Rep.{0} (ZMod 3) B) [FiniteDimensional (ZMod 3) A]
    (E : OriginalKernelModuleChart pi A)
    (hu : UniformSubrepresentationGeneratorBound A.ρ 1)
    (k : ℕ) (hcard : Nat.card B∣2^k*3)
    (hB : SocleNormalGeneratorBound B 2) : SocleNormalGeneratorBound G 2 := by
  let P := minimalNormalSoclePart G (fun M => IsPGroup 3 M)
  have hp : IsPGroup 3 P := minimalNormalSoclePart_isPGroup 3 G _ (fun _ _ h => h)
  have hker : IsPGroup 3 pi.ker :=
    (ZModModule.isPGroup_multiplicative (n := 3) (G := A)).of_surjective
      E.equiv.toMonoidHom E.equiv.surjective
  have hK : MarkedC4.normalGen (P ⊓ pi.ker)≤1 :=
    E.kernel_normalGen_le pi A hpi 1 hu _ inf_le_right
  letI : (P.map pi).Normal := Subgroup.Normal.map inferInstance pi hpi
  have hpiP : IsPGroup 3 (P.map pi) := hp.map pi
  obtain ⟨n,hn⟩ := hpiP.exists_card_eq
  have hcop : Nat.Coprime (Nat.card (P.map pi)) (2^k) := by
    rw [hn]
    exact ((by decide : Nat.Coprime 3 2).pow_left n).pow_right k
  have hd : Nat.card (P.map pi)∣3 := hcop.dvd_of_dvd_mul_left
    ((P.map pi).card_subgroup_dvd_card.trans hcard)
  have hr : Module.finrank (ZMod 3) (PrimeCharacters 3 (P.map pi))≤1 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1<3)).mp
    exact (primeCharacters_pow_finrank_le_card 3 (P.map pi)).trans
      (by simpa only [pow_one] using Nat.le_of_dvd (by decide : 0<3) hd)
  have hI : MarkedC4.normalGen (P.map pi)≤1 :=
    (MarkedC4.normalGen_normalSubgroup_le_primeCharacterRank 3 (P.map pi) hpiP).trans hr
  have hP : MarkedC4.normalGen P≤2 :=
    normalGen_le_actual_intersection_add_image pi hpi P 1 1 hK hI
  let T := minimalNormalSoclePart G (fun M => ¬ IsPGroup 3 M)
  have he : T=minimalNormalSoclePart G
      (fun M => ¬ IsPGroup 3 M ∧ IsMulCommutative M) := by
    apply minimalNormalSoclePart_congr
    intro M hM
    exact ⟨fun h => ⟨h,minimalNormal_isMulCommutative_of_isSolvable M hM⟩,And.left⟩
  have hdis : T ⊓ pi.ker=⊥ := by
    rw [he]
    exact abelianNonPrimarySoclePart_inf_isPGroup_eq_bot 3 pi.ker hker
  letI : (T.map pi).Normal := Subgroup.Normal.map inferInstance pi hpi
  have hle : T.map pi≤finiteGroupSocle B :=
    (Subgroup.map_mono (minimalNormalSoclePart_le_finiteGroupSocle _ _)).trans
      (SocleActionPartQuotientKernel.socle_map_le pi hpi)
  have hT : MarkedC4.normalGen T≤2 :=
    (normalGen_le_image_of_disjoint_kernel pi hpi T hdis).trans
      ((MarkedC4.normalGen_le_socle_of_normal_le (T.map pi) hle).trans
        ((socleNormalGeneratorBound_iff_normalGen_le B 2).mp hB))
  apply (socleNormalGeneratorBound_iff_normalGen_le G 2).mpr
  exact (normalGen_finiteGroupSocle_le_max_primePrimaryParts 3 G).trans (max_le hP hT)

end SymmetricSubgroupAsymptotics.CubicKernelSingleTopSocleTwo
