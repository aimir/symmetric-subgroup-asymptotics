import SymmetricSubgroupAsymptotics.SixPairOriginalBinaryQuotientCard
import SymmetricSubgroupAsymptotics.CubicKernelCoordinateEnvelope
import SymmetricSubgroupAsymptotics.CubicOriginalNormalQuotientChart
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairCharacterOnlySource

/-! All original quotients above an actual cubic elementary kernel.
Nonbinary quotients retain a quotient of the SAME kernel module. Those
meeting the cubic top are binary and use the unconditional six-pair32
bound. No nonzero-scalar or self-centralizer premise is needed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace SixPairNonbinaryQuotientCubic

variable {G : Type} [Group G] [Finite G]
    (top : G →* CyclicThree) (hK : IsPGroup 2 top.ker)
    (N : Subgroup G) [N.Normal]

include hK in
/-- Any actual normal subgroup meeting the cubic top leaves a binary
original quotient, without a splitting or centralizer assumption. -/
theorem binary_of_not_le_kernel (hN : ¬ N ≤ top.ker) : IsPGroup 2 (G ⧸ N) := by
  have honto : Function.Surjective (top.comp N.subtype) := by
    letI : Fact (Nat.card CyclicThree).Prime := ⟨by
      norm_num [CyclicThree,Nat.card_eq_fintype_card]⟩
    apply MonoidHom.range_eq_top.mp
    apply (top.comp N.subtype).range.eq_bot_or_eq_top_of_prime_card.resolve_left
    intro hb
    apply hN
    intro n hn
    apply MonoidHom.mem_ker.mpr
    have hm : top n ∈ (top.comp N.subtype).range := ⟨⟨n,hn⟩,rfl⟩
    rw [hb] at hm
    exact Subgroup.mem_bot.mp hm
  let f : top.ker →* G ⧸ N := (QuotientGroup.mk' N).comp top.ker.subtype
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective N q
    obtain ⟨n,hn⟩ := honto (top g)
    have hk : g*(n : G)⁻¹ ∈ top.ker := by
      rw [MonoidHom.mem_ker,map_mul,map_inv]
      have hn' : top (n : G) = top g := hn
      rw [hn',mul_inv_cancel]
    refine ⟨⟨g*(n : G)⁻¹,hk⟩,?_⟩
    change QuotientGroup.mk' N (g*(n : G)⁻¹) = QuotientGroup.mk' N g
    have hz : QuotientGroup.mk' N (n : G) = 1 :=
      (QuotientGroup.eq_one_iff (N := N) (n : G)).mpr n.2
    rw [map_mul,map_inv,hz,inv_one,mul_one]
  exact hK.of_surjective f hf

include hK in
theorem nonbinary_le_kernel (hQ : ¬ IsPGroup 2 (G ⧸ N)) : N ≤ top.ker := by
  by_contra hn
  exact hQ (binary_of_not_le_kernel top hK N hn)

section Original
variable {U : Subgroup (Equiv.Perm (Fin 12))}
    [MulAction.IsPretransitive U (Fin 12)]
    (F : BinaryPairFrame U (Fin 6))
    (t : U →* CyclicThree) (ht : Function.Surjective t)
    (A : Rep (ZMod 2) CyclicThree) (E : OriginalKernelModuleChart t A)
    (D : CubicBinaryCoordinates A.ρ)

include F t ht A E D

/-- Every actual original quotient is certified from the same original
joint module coordinates, including zero-scalar and central cases. -/
def quotientCertificate (hKP : KovacsPraegerAbelianizationBound)
    (M : Subgroup U) [M.Normal] : PreE7B6QuotientCertificate (U ⧸ M) := by
  by_cases hQ : IsPGroup 2 (U ⧸ M)
  · exact F.original_binary_quotient_B6_certificate M hQ
  · have hk : IsPGroup 2 t.ker :=
      (ZModModule.isPGroup_multiplicative (n := 2) (G := A)).of_injective
        E.equiv.symm.toMonoidHom E.equiv.symm.injective
    have hm : M ≤ t.ker := nonbinary_le_kernel t hk M hQ
    let qtop := QuotientGroup.lift M t hm
    have hqtop : Function.Surjective qtop := by
      intro c
      obtain ⟨g,hg⟩ := ht c
      exact ⟨QuotientGroup.mk' M g,hg⟩
    let B := CubicOriginalNormalQuotientChart.quotientModule t ht A E M
    let C := CubicOriginalNormalQuotientChart.quotientChart t ht A E M hm
    let J := CubicOriginalNormalQuotientChart.quotientCoordinates t ht A E M D
    exact CubicKernelCoordinateEnvelope.certificate qtop hqtop B C J hKP

/-- Direct exact source constructor; no global table or locator is filled. -/
def actionCertificate (hKP : KovacsPraegerAbelianizationBound) :
    Non2UnipotentPrefixFiniteMenu.PreE7B6ActionCertificate U where
  blockChart := Non2UnipotentPrefixFiniteMenu.sixPairBlockChart F
  preserves := Non2UnipotentPrefixFiniteMenu.sixPairBlockChart_preserves F
  quotient M := quotientCertificate F t ht A E D hKP M.1

end Original
end SixPairNonbinaryQuotientCubic
end SymmetricSubgroupAsymptotics
end
