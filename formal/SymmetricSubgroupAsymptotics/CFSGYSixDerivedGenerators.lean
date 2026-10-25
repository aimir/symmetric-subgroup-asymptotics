import SymmetricSubgroupAsymptotics.CFSGYArmProductGeneration
import SymmetricSubgroupAsymptotics.DerivedInvolutionCosetOrdinaryGenerators

/-! SIX ordinary generators for the ACTUAL derived subgroup of any original
Y group and its FULL centre quotient. The three displayed arm products
are normalized by the corresponding power of the central involution;
equal original abelianization images make these literal derived elements.
Together with the original central involution they generate the full Y
group. The involutory Schreier family therefore has six elements.
No finite/order/simple/model callback or abstract head premise is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGYSixDerivedGenerators
open CFSG.Models.YGroups CFSGGeneration CFSGReduction CFSGYArmProductGeneration

private abbrev centralGenerator (arms : Arms) : CFSG.Models.YGroups.Group arms :=
  PresentedGroup.of (rels := relations arms) none

private theorem abelianization_arm_product (arms : Arms) (i : Fin 3) :
    Abelianization.of (armProduct arms i) =
      (Abelianization.of (centralGenerator arms))^(arms.length i) := by
  rw [armProduct,armList,map_list_prod,List.map_ofFn]
  change (List.ofFn (fun d : Fin (arms.length i) =>
    Abelianization.of (PresentedGroup.of (rels := relations arms) (some ⟨i,d⟩)))).prod = _
  simp only [y_abelianization_generators_equal,List.ofFn_const,List.prod_replicate]

/-- The SAME three arm products, normalized into the original derived group. -/
def derivedArmProduct (arms : Arms) (i : Fin 3) :
    commutator (CFSG.Models.YGroups.Group arms) := by
  refine ⟨armProduct arms i*(centralGenerator arms)^(arms.length i),?_⟩
  rw [← Abelianization.ker_of (CFSG.Models.YGroups.Group arms)]
  change Abelianization.of (armProduct arms i*(centralGenerator arms)^(arms.length i)) = 1
  rw [map_mul,map_pow,abelianization_arm_product,← pow_add]
  have hs : (Abelianization.of (centralGenerator arms))^2 = 1 := by
    rw [← map_pow,y_generator_sq,map_one]
  rw [← two_mul,pow_mul,hs,one_pow]

/-- Original full-Y generation is retained before ordinary derived
Schreier generation; no quotient has been substituted for the source. -/
theorem normalized_generators_generate (arms : Arms) :
    Subgroup.closure (Set.range (fun i => (derivedArmProduct arms i : CFSG.Models.YGroups.Group arms)) ∪
      {centralGenerator arms}) = ⊤ := by
  let H := Subgroup.closure
    (Set.range (fun i => (derivedArmProduct arms i : CFSG.Models.YGroups.Group arms)) ∪
      {centralGenerator arms})
  have hr : centralGenerator arms ∈ H := Subgroup.subset_closure (Or.inr rfl)
  have hc (i : Fin 3) : armProduct arms i ∈ H := by
    have hg : (derivedArmProduct arms i : CFSG.Models.YGroups.Group arms) ∈ H :=
      Subgroup.subset_closure (Or.inl ⟨i,rfl⟩)
    have hh := H.mul_mem hg (H.inv_mem (H.pow_mem hr (arms.length i)))
    change (armProduct arms i*(centralGenerator arms)^(arms.length i))*
      ((centralGenerator arms)^(arms.length i))⁻¹ ∈ H at hh
    simpa only [mul_inv_cancel_right] using hh
  apply top_unique
  rw [← fourGenerators_generate arms]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨k,rfl⟩
  refine Fin.cases ?_ ?_ k
  · exact hr
  · intro i
    exact hc i

theorem exists_derived_generating_finset (arms : Arms) :
    ∃ S : Finset (commutator (CFSG.Models.YGroups.Group arms)),
      Subgroup.closure (S : Set (commutator (CFSG.Models.YGroups.Group arms))) = ⊤ ∧ S.card ≤ 6 := by
  obtain ⟨S,hS,hcard⟩ := DerivedInvolutionCosetOrdinaryGenerators.exists_generating_finset
    (derivedArmProduct arms) (centralGenerator arms) (normalized_generators_generate arms)
    (y_generator_sq arms none)
  exact ⟨S,hS,by simpa only [Nat.card_fin] using hcard⟩

theorem derived_genRank_le_six (arms : Arms) :
    MarkedC4.genRank (commutator (CFSG.Models.YGroups.Group arms)) ≤ 6 := by
  obtain ⟨S,hS,hcard⟩ := exists_derived_generating_finset arms
  exact (MarkedC4.genRank_le hS).trans hcard

/-- Push the SAME derived generating family through its FULL centre quotient. -/
theorem exists_simple_section_generating_finset (arms : Arms) :
    ∃ S : Finset (SimpleSection arms),
      Subgroup.closure (S : Set (SimpleSection arms)) = ⊤ ∧ S.card ≤ 6 := by
  exact generators_card_le_of_surjective (QuotientGroup.mk' _)
    (QuotientGroup.mk'_surjective _) (exists_derived_generating_finset arms)

theorem simple_section_genRank_le_six (arms : Arms) :
    MarkedC4.genRank (SimpleSection arms) ≤ 6 := by
  obtain ⟨S,hS,hcard⟩ := exists_simple_section_generating_finset arms
  exact (MarkedC4.genRank_le hS).trans hcard

end SymmetricSubgroupAsymptotics.CFSGYSixDerivedGenerators
