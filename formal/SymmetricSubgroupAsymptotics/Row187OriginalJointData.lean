import SymmetricSubgroupAsymptotics.Row187OriginalPairFrame
import SymmetricSubgroupAsymptotics.CyclicSixPairSingletonTopOriginalSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlexibleProfiles
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
set_option autoImplicit false
set_option maxRecDepth 8192
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row187OriginalJointData
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open Row187OriginalPairFrame

private def pairElement : frame.top.range :=
  ⟨cycleWord.eval tops,⟨cycleWord.eval original,word_top cycleWord⟩⟩
private theorem pair_cover : ∀ x : Fin 6,∃ n : Fin 6,pairElement^n.val • (0 : Fin 6)=x := by
  decide +kernel
private theorem pair_uniform : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) frame.top.range (Fin 6)) 1 := by
  apply permutationFunctionRepresentation_uniform_of_polynomial_orbitCover pairElement (fun _ : Fin 1 => (0 : Fin 6))
  intro x
  obtain ⟨n,hn⟩ := pair_cover x
  exact ⟨0,n.val,hn⟩
private theorem top_singletons : ∀ L : Subgroup frame.top.range,L.Normal →
    ∃ x : Fin 1 → frame.top.range,Subgroup.normalClosure (Set.range x)=L :=
  normal_generating_tuples_of_surjective topEquiv.toMonoidHom topEquiv.surjective
    AlternatingFourCentralTwoSocles.normal_generating_singletons

theorem quotientSocle (N : Subgroup row187Interface.top) [N.Normal] :
    SocleNormalGeneratorBound (row187Interface.top ⧸ N) 2 :=
  CyclicSixPairSingletonTopOriginalSocles.quotientSocle_of_uniform_top frame pair_uniform top_singletons N

private theorem point_cover : ∀ x : Fin 12,∃ j : Fin 2,∃ n : Fin 12,
    (cycleWord.eval original)^n.val • points (0,(j.val : ZMod 2))=x := by
  decide +kernel

theorem natural_two : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row187Interface.top (Fin 12)) 2 := by
  apply permutationFunctionRepresentation_uniform_of_polynomial_orbitCover
    (cycleWord.eval original) (fun j : Fin 2 => points (0,(j.val : ZMod 2)))
  intro x
  obtain ⟨j,n,hn⟩ := point_cover x
  exact ⟨j,n.val,hn⟩

def jointData : DegreeTwoTwelveJointFiniteRows.DegreeTwoTwelveJointFiniteRowData row187Interface 2 2 where
  topSocle := FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds _ (fun N => by
    letI := N.2
    exact quotientSocle N.1)
  natural := natural_two
def flexibleData : DegreeTwoTwelveFlexibleProfiles.Data row187Interface :=
  .ofExact jointData (by decide +kernel)
end SymmetricSubgroupAsymptotics.Row187OriginalJointData
