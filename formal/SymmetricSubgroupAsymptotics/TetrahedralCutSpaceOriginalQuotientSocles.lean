import SymmetricSubgroupAsymptotics.TetrahedralCutSpaceOriginalInsideSocle
import SymmetricSubgroupAsymptotics.AlternatingEdgeOriginalOddSocles
import SymmetricSubgroupAsymptotics.AlternatingFourNontrivialQuotientOrder
import SymmetricSubgroupAsymptotics.OriginalBinaryKernelCubicLift
import SymmetricSubgroupAsymptotics.OriginalKernelIntersectionProjectorRanks
import SymmetricSubgroupAsymptotics.OriginalElementaryImageRange
import SymmetricSubgroupAsymptotics.NaturalFourCubicNormalImage
import SymmetricSubgroupAsymptotics.SelectedBinarySocleCubicIntersectionOne
import SymmetricSubgroupAsymptotics.PrimePrimarySocleTypeSharing

/-! Every ORIGINAL normal quotient of an elementary binary extension
with its literal full tetrahedral cut module has socle bound1.
No split lift, normal menu, or capacity premise is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TetrahedralCutSpaceOriginalQuotientSocles
open AlternatingEdgeOriginalProjectorHeads (Top a beta)
open OriginalKernelModuleChart
open TetrahedralCutSpaceOriginalHeads (R)
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem quotientSocle {G : Type} [Group G] [Finite G]
    (pi : G →* Top) (hpi : Function.Surjective pi)
    (E : OriginalKernelModuleChart pi R)
    (N : Subgroup G) [N.Normal] : SocleNormalGeneratorBound (G ⧸ N) 1 := by
  letI : FiniteDimensional (ZMod 2) (E.sectionRepresentation pi R N) := by
    change FiniteDimensional (ZMod 2) (E.sectionModule pi R N)
    infer_instance
  have ha : a^3=1 := by decide +kernel
  rcases TetrahedralCutSpaceOriginalHeads.outside_heads pi hpi E N with hinside | ⟨hfixed,hactive⟩
  · exact TetrahedralCutSpaceOriginalInsideSocle.socle_bound pi hpi E N hinside
  let f := sectionTop pi N hpi
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (pi.ker ⊔ N) x
    exact ⟨pi g,sectionTop_apply pi N hpi g⟩
  by_cases hinside : finiteGroupSocle (G ⧸ N) ≤ (base pi N).ker
  · exact TetrahedralCutSpaceOriginalInsideSocle.socle_bound pi hpi E N hinside
  have hfn : ∃ b, f b≠1 := by
    by_contra hn
    push Not at hn
    apply hinside
    intro x _hx
    change base pi N x=1
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective N x
    rw [base_apply,← sectionTop_apply pi N hpi g]
    exact hn (pi g)
  have h3 := AlternatingFourNontrivialQuotientOrder.three_dvd f hf hfn
  have han : a≠1 := by decide +kernel
  obtain ⟨g,hg,hpg⟩ := E.exists_original_cubic_lift pi R hpi a ha
  let q := QuotientGroup.mk' N
  let z := q g
  have hz : z^3=1 := by rw [← map_pow,hg,map_one]
  have hbase : base pi N z=f a := by
    change QuotientGroup.mk' (pi.ker ⊔ N) g=f a
    rw [← sectionTop_apply pi N hpi g,hpg]
  have hzn : z≠1 := by
    intro h
    have hh := congrArg (base pi N) h
    rw [hbase,map_one] at hh
    exact AlternatingFourNontrivialQuotientOrder.cubic_survives f hfn a ha han hh
  let C := selectedPrimeSoclePartElementaryChart 2 (G := G ⧸ N) (fun _ => True)
  let S := C.originalKernelChart
  letI : FiniteDimensional (ZMod 2) C.quotientRepresentation := C.finiteDimensional
  have hke := S.kernelIntersection_fixed_projector_rank_le (base pi N)
    (E.quotientChart pi R N) z
  have hkf := S.kernelIntersection_active_rank_le (base pi N)
    (E.quotientChart pi R N) z
  rw [hbase] at hke hkf
  have hL := S.elementaryImage_normal (base pi N) (base_surjective pi N)
  have hpL := S.elementaryImage_isPGroup_two (base pi N)
  have hcard := NaturalFourCubicNormalImage.alternating_card_le_four f hf h3
    (S.elementaryImageHom (base pi N)).range hL hpL
  have hfix : ∀ x∈(S.elementaryImageHom (base pi N)).range,
      base pi N z*x*(base pi N z)⁻¹=x → x=1 := by
    intro x hx he
    rw [hbase] at he
    exact NaturalFourCubicNormalImage.alternating_fixed_eq_one f hf h3
      (S.elementaryImageHom (base pi N)).range hL hpL a ha han x hx he
  have hb : MarkedC4.normalGen
      (minimalNormalSoclePart (G ⧸ N) (fun M => IsPGroup 2 M))≤1 :=
    SelectedBinarySocleCubicIntersectionOne.normalGen_le_one (base pi N) z hz hzn
      (hke.trans hfixed) (hkf.trans hactive) hcard hfix
  have ho := AlternatingEdgeOriginalOddSocles.normalGen_le_one pi hpi R E N
  have hs := normalGen_finiteGroupSocle_le_max_primePrimaryParts 2 (G ⧸ N)
  apply (socleNormalGeneratorBound_iff_normalGen_le (G ⧸ N) 1).mpr
  exact hs.trans (max_le hb ho)

end SymmetricSubgroupAsymptotics.TetrahedralCutSpaceOriginalQuotientSocles
