import SymmetricSubgroupAsymptotics.PrimeTranslationFrame
import SymmetricSubgroupAsymptotics.ElementaryNormalModuleGenerators
import SymmetricSubgroupAsymptotics.LinearSemidirectUniformNormalGenerators
import SymmetricSubgroupAsymptotics.RepresentationDualSubquotientGenerators
import SymmetricSubgroupAsymptotics.RepresentationGeneratorRestrictionMaschke
import SymmetricSubgroupAsymptotics.PGroupCoinvariantGenerators
import SymmetricSubgroupAsymptotics.NormalGeneratorActualIntersectionImage

/-! Actual prime-translation kernel normal generators. This is uniform
over every original ambient-normal subgroup of the kernel, rather than
only the kernel itself. It supplies the odd-prime ordinary recurrence
needed by the independent subgroup-counting route. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimeTranslationFrame
variable {p : ℕ} [Fact p.Prime] {X I : Type} [Finite X] [Finite I]
    {U : Subgroup (Equiv.Perm X)} (F : PrimeTranslationFrame p U I)
    [MulAction U I] (hact : ∀ (u : U) (i : I),u • i=F.top u i)

def ordinaryNormalGenerationChart : ElementaryMinimalNormalChart F.top.ker := by
  letI := Fintype.ofFinite I
  exact { p := p, p_prime := (Fact.out : p.Prime),V := F.kernelSpace,equiv := F.kernelChart }

include hact

def ordinaryNormalGenerationInclusion :
    (show Representation (ZMod p) U F.kernelSpace from
      F.ordinaryNormalGenerationChart.quotientRepresentation.ρ.comp
        (QuotientGroup.mk' F.top.ker)).IntertwiningMap
      (permutationFunctionRepresentation (ZMod p) U I) where
  toLinearMap := F.kernelSpace.subtype
  isIntertwining' u := by
    apply LinearMap.ext
    intro v
    obtain ⟨k,hk⟩ := F.kernelChart.surjective (Multiplicative.ofAdd v)
    have hv : (F.kernelChart k).toAdd=v := congrArg Multiplicative.toAdd hk
    rw [←hv]
    change F.kernelSpace.subtype
      (F.ordinaryNormalGenerationChart.quotientRepresentation.ρ
        (QuotientGroup.mk' F.top.ker u)
        ((F.ordinaryNormalGenerationChart.equiv k).toAdd)) = _
    rw [ElementaryMinimalNormalChart.quotientRepresentation_apply]
    change F.bits (MulAut.conjNormal u k)=
      permutationFunctionRepresentation (ZMod p) U I u (F.bits k)
    exact (F.originalCoordinateAction_bits hact u k).symm

theorem normalGen_le_of_uniform_module (a : ℕ)
    (huniform : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod p) U I) a)
    (N : Subgroup U) [N.Normal] (hN : N≤F.top.ker) : MarkedC4.normalGen N≤a := by
  have hquot : UniformSubrepresentationGeneratorBound
      F.ordinaryNormalGenerationChart.quotientRepresentation.ρ a := by
    apply UniformSubrepresentationGeneratorBound.of_comp
      F.ordinaryNormalGenerationChart.quotientRepresentation.ρ (QuotientGroup.mk' F.top.ker)
    exact huniform.of_injective (ordinaryNormalGenerationInclusion F hact)
      F.kernelSpace.subtype_injective
  exact ElementaryUniformNormalGenerators.kernel_normalGen_le
    F.top.ker F.ordinaryNormalGenerationChart a hquot N hN

/-- The full label space gives a uniform bound even at degree one. -/
theorem normalGen_le_card (hU : IsPGroup p U)
    (N : Subgroup U) [N.Normal] (hN : N≤F.top.ker) : MarkedC4.normalGen N≤Nat.card I := by
  letI : Fintype I := Fintype.ofFinite I
  apply F.normalGen_le_of_uniform_module hact (Nat.card I) _ N hN
  apply pGroup_uniformSubrepresentationGeneratorBound_of_head_le hU
  intro M
  have h := subrepresentationHead_le_ambient_elementFixedSpace
    (permutationFunctionRepresentation (ZMod p) U I) M (1 : U)
  have h' := h.trans (Submodule.finrank_le
    (representationElementFixedSpace (permutationFunctionRepresentation (ZMod p) U I) 1))
  simpa only [Module.finrank_pi,Nat.card_eq_fintype_card] using h'

/-- A nontrivial actual transitive top gives the uniform degree/p bound. -/
theorem normalGen_le_div [Nontrivial I] [MulAction.IsPretransitive U I]
    (hU : IsPGroup p U) (N : Subgroup U) [N.Normal] (hN : N≤F.top.ker) :
    MarkedC4.normalGen N≤Nat.card I/p := by
  letI : Fintype I := Fintype.ofFinite I
  apply F.normalGen_le_of_uniform_module hact (Nat.card I/p) _ N hN
  apply pGroup_uniformSubrepresentationGeneratorBound_of_head_le hU
  intro M
  exact pGroup_permutationSubrepresentationHead_le_div hU M

/-- The original normal is split only into its actual intersection with
this kernel and actual image under this same top homomorphism. -/
theorem normalGen_le_div_add_actual_image [Nontrivial I] [MulAction.IsPretransitive U I]
    (hU : IsPGroup p U) (N : Subgroup U) [N.Normal] :
    MarkedC4.normalGen N≤Nat.card I/p+MarkedC4.normalGen (N.map F.top.rangeRestrict) := by
  have hk : F.top.rangeRestrict.ker=F.top.ker := MonoidHom.ker_rangeRestrict F.top
  apply normalGen_le_actual_intersection_add_image F.top.rangeRestrict
    F.top.rangeRestrict_surjective N (Nat.card I/p)
    (MarkedC4.normalGen (N.map F.top.rangeRestrict)) _ le_rfl
  rw [hk]
  exact F.normalGen_le_div hact hU (N ⊓ F.top.ker) inf_le_right

end SymmetricSubgroupAsymptotics.PrimeTranslationFrame
