import SymmetricSubgroupAsymptotics.PrimitiveSixOriginalQuotientDichotomy
import SymmetricSubgroupAsymptotics.PrimitiveDegreeSixActualNormalConsumers

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveSixOriginalQuotientDichotomy.DirectSix
open OriginalKernelModuleChart

local instance primitiveSixDichotomy_binaryPrimeFact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {G B : Type} [Group G] [Finite G] [Group B] [Finite B]
  [act : MulAction B (Fin 6)] [faithful : FaithfulSMul B (Fin 6)]
  [primitive : MulAction.IsPreprimitive B (Fin 6)]
  (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
  (pi : G →* B) (hpi : Function.Surjective pi)
  (A : Rep.{0} (ZMod 2) B) [Finite A] [FiniteDimensional (ZMod 2) A]
  (E : OriginalKernelModuleChart pi A)
  (hu : UniformSubrepresentationGeneratorBound A.ρ 1)

include hindex pi hpi A E hu act faithful primitive in
/-- Exhaustive alternatives on the unchanged quotient by the original N. -/
theorem quotientAlternative (N : Subgroup G) [N.Normal] :
    SocleNormalGeneratorBound (G ⧸ N) 1 ∨
      (IsPGroup 2 (G ⧸ N) ∧ Nat.card (G ⧸ N) ≤ 8) := by
  let R := G ⧸ (pi.ker ⊔ N)
  let f : (G ⧸ N) →* R := base pi N
  let S : Rep.{0} (ZMod 2) R := E.sectionRepresentation pi A N
  letI : Finite S := by
    change Finite (E.sectionModule pi A N)
    exact Finite.of_surjective (E.sectionProjection pi A N)
      (E.sectionProjection_surjective pi A N)
  let C : OriginalKernelModuleChart f S := E.quotientChart pi A N
  have hf : Function.Surjective f := base_surjective pi N
  have hs : Function.Surjective (sectionTop pi N hpi) := by
    intro r
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (pi.ker ⊔ N) r
    exact ⟨pi g,sectionTop_apply pi N hpi g⟩
  have hprops :
      (∀ L : Subgroup B,L.Normal → IsMulCommutative L → L=⊥) ∧
      (∀ L : Subgroup B,L.Normal → L≠⊥ → Nat.card (B⧸L)≤2) :=
    ⟨PrimitiveDegreeSixActualNormalConsumers.noAbelianNormal hindex,
      PrimitiveDegreeSixActualNormalConsumers.normal_quotient_card_le_two hindex⟩
  by_cases hN : N ≤ pi.ker
  · left
    have hi : Function.Injective (sectionTop pi N hpi) := by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      apply le_antisymm _ bot_le
      intro b hb
      obtain ⟨g,rfl⟩ := hpi b
      change sectionTop pi N hpi (pi g)=1 at hb
      have hz : QuotientGroup.mk' (pi.ker ⊔ N) g=1 :=
        (sectionTop_apply pi N hpi g).symm.trans hb
      have hg : g∈pi.ker ⊔ N := (QuotientGroup.eq_one_iff _).mp hz
      rw [sup_eq_left.mpr hN] at hg
      exact Subgroup.mem_bot.mpr hg
    let e : B ≃* R := MulEquiv.ofBijective (sectionTop pi N hpi) ⟨hi,hs⟩
    have hc : IsMulCommutative f.ker := IsMulCommutative.of_comm fun x y => by
      apply C.equiv.symm.injective
      rw [map_mul,map_mul,mul_comm]
    have huS : UniformSubrepresentationGeneratorBound S.ρ 1 := E.sectionUniform pi A N hpi hu
    have hkernel (L : Subgroup (G ⧸ N)) (hL : L.Normal) (hle : L ≤ f.ker) :
        MarkedC4.normalGen L ≤ 1 := by
      letI := hL
      exact C.kernel_normalGen_le f S hf 1 huS L hle
    have htopB (L : Subgroup B) (hL : L.Normal) : MarkedC4.normalGen L ≤ 1 := by
      letI := hL
      exact PrimitiveDegreeSixActualNormalConsumers.normalGen_le_one hindex L
    have htop (L : Subgroup R) (hL : L.Normal) : MarkedC4.normalGen L ≤ 1 := by
      letI := hL
      exact CoprimeKernelQuotientSocles.normalGen_image_bound
        e.toMonoidHom e.surjective 1 htopB L
    exact PrimitiveSixSocleMapBridge.socle_le_max_of_map f hf hc 1 1 hkernel
      (PrimitiveSixSocleMapBridge.noAbelianNormal_of_equiv e.symm hprops.1) htop
  · right
    letI : (N.map pi).Normal := (inferInstance : N.Normal).map pi hpi
    have hne : N.map pi≠⊥ := by
      intro hz
      exact hN ((Subgroup.map_eq_bot_iff (H := N)).mp hz)
    have hsmall : Nat.card R ≤ 2 :=
      (residualTop_card_eq pi hpi N).le.trans (hprops.2 (N.map pi) inferInstance hne)
    have hR : IsPGroup 2 R := by
      have hp : 0 < Nat.card R := Nat.card_pos
      by_cases hcard : Nat.card R=1
      · exact IsPGroup.of_card (n := 0) (by simpa using hcard)
      · have htwo : Nat.card R = 2 := by omega
        exact IsPGroup.of_card (n := 1) (by simpa only [pow_one] using htwo)
    have hk : IsPGroup 2 f.ker :=
      (ZModModule.isPGroup_multiplicative (n := 2) (G := S)).of_equiv C.equiv
    have hQ : IsPGroup 2 (G ⧸ N) := by
      have ht := (hR.to_subgroup (⊤ : Subgroup R)).comap_of_ker_isPGroup f hk
      have ht' : IsPGroup 2 (⊤ : Subgroup (G ⧸ N)) := by
        simpa only [Subgroup.comap_top] using ht
      exact ht'.of_equiv Subgroup.topEquiv
    let idMap : Representation.IntertwiningMap A.ρ A.ρ :=
      { toLinearMap := LinearMap.id, isIntertwining' _ := rfl }
    have hgen : RepresentationGeneratedBy A.ρ 1 :=
      representationGeneratedBy_of_injective_of_uniform hu idMap (fun _ _ h => h)
    exact ⟨hQ,E.quotient_card_le_eight_of_cyclic_small_top pi hpi A N hgen hsmall⟩

include hindex pi hpi A E hu act faithful primitive in
/-- The historical B6 target alternatives, constructed before inspecting
any source group, with the original normal denominator unchanged. -/
def quotientCertificate (hZmud : ZmudFaithfulCharacterTupleInput)
    (N : Subgroup G) [N.Normal] : PreE7B6QuotientCertificate (G ⧸ N) := by
  have h := quotientAlternative hindex pi hpi A E hu N
  by_cases hsoc : SocleNormalGeneratorBound (G ⧸ N) 1
  · let c := hZmud.generalCertificate hsoc
    apply PreE7B6QuotientCertificate.character c
    apply CharacterQuotientCertificate.slope_le_four_thirds_of_mixed c rfl rfl
    change 3 ^ 0 * 5 ^ 1 ≤ 15
    norm_num
  · have hb := h.resolve_left hsoc
    exact .binary hb.1 (hb.2.trans (by decide : 8 ≤ 32))


end SymmetricSubgroupAsymptotics.PrimitiveSixOriginalQuotientDichotomy.DirectSix
