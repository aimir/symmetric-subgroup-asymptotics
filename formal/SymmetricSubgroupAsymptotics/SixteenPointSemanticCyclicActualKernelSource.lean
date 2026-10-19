import SymmetricSubgroupAsymptotics.BinaryPlaneCyclicActualKernelQuotientSocles
import SymmetricSubgroupAsymptotics.PreE7FiniteMixedPermutationMenu

/-! Complete original-weight sixteen-point source for an actual nonbinary
cyclic binary-plane kernel chart. Every original normal quotient is proved
structurally before the census-free weighted source constructor is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.SixteenPointSemanticCyclicActualKernelSource
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {R I G : Type} [Group R] [Finite R] [IsCyclic R] [MulAction R I]
  [Fintype I] [DecidableEq I] [Group G] [Finite G]
  (C : Subgroup (W (R := R) (I := I)))
  (pi : G →* C) (hpi : Function.Surjective pi)
  (A : Rep.{0} (ZMod 2) C) (E : OriginalKernelModuleChart pi A)
  [FiniteDimensional (ZMod 2) A]
  (j : Representation.IntertwiningMap A.ρ (BinaryPlaneCyclicWreathUniform.representation C))
  (hj : Function.Injective j)
  (hsurj : Function.Surjective
    ((PermutationalWreathProduct.rightHom : W (R := R) (I := I) →* R).comp C.subtype))
  (c : R) (i₀ : I) (hcycle : ∀ i : I, ∃ n : ℕ, c^n • i₀=i)
  (hR : IsPGroup 2 R) (hG : ¬ IsPGroup 2 G)

include C pi hpi A E j hj hsurj c i₀ hcycle hR hG in
/-- Any displayed actual quotient keeps its complete socle bound two. -/
theorem socle_of_surjective {Q : Type} [Group Q]
    (phi : G →* Q) (hphi : Function.Surjective phi) : SocleNormalGeneratorBound Q 2 := by
  letI : Finite Q := Finite.of_surjective phi hphi
  have hbound := BinaryPlaneCyclicActualKernelQuotientSocles.quotientSocle
    C pi hpi A E j hj hsurj c i₀ hcycle hR hG phi.ker
  exact CyclicSocleQuotientTools.socleBound_equiv
    (QuotientGroup.quotientKerEquivOfSurjective phi hphi) hbound

include C pi hpi A E j hj hsurj c i₀ hcycle hR hG in
/-- The actual marking and weights are the supplied original row's. There
is no recursive invocation of the count-eight endpoint at width sixteen. -/
def source (i : PreE7NonPairActionClass 16)
    (phi : G →* preE7NonPairAction 16 i) (hphi : Function.Surjective phi)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    PreE7RankTailSourceOrYonedaTopData 16 i := by
  let row : DegreeTwoDegreeSixteenImportedRow i :=
    PreE7FiniteMixedPermutationMenu.censusFreeImportedRow hMN i (by decide : 2≤2)
      (fun N => by
        letI := N.2
        exact socle_of_surjective C pi hpi A E j hj hsurj c i₀ hcycle hR hG
          ((QuotientGroup.mk' N.1).comp phi)
          ((QuotientGroup.mk'_surjective N.1).comp hphi)) hZmud
  exact row.source

end SymmetricSubgroupAsymptotics.SixteenPointSemanticCyclicActualKernelSource
