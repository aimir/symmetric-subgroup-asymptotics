import SymmetricSubgroupAsymptotics.Row74PairProjectionGraph
import SymmetricSubgroupAsymptotics.Row74OriginalPrimitivePairTop
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row74OriginalFaithfulPairTop
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open Row74OriginalSixPairFrame
open Row74OriginalPrimitivePairTop (original)

def generators : Fin 4 → row74Interface.top :=
  ![original 0,original 1,(original 0)⁻¹,(original 1)⁻¹]
private theorem generators_full : Subgroup.closure (Set.range generators)=⊤ := by
  have h : Subgroup.closure (Set.range original)≤Subgroup.closure (Set.range generators) := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    fin_cases i
    · exact Subgroup.subset_closure (Set.mem_range_self 0)
    · exact Subgroup.subset_closure (Set.mem_range_self 1)
  rw [show Subgroup.closure (Set.range original)=⊤ from closureGenerators_full row74Generators] at h
  exact top_unique h

def paired : row74Interface.top →* Equiv.Perm (Fin 6) × Equiv.Perm (Fin 12) :=
  frame.top.prod row74Interface.top.subtype
private theorem paired_injective : Function.Injective paired := by
  intro u v h
  apply Subtype.ext
  exact congrArg Prod.snd h
private theorem generator_binding (i : Fin 4) :
    paired (generators i)=(Row74PairProjectionGraph.sourceGenerators i,
      Row74PairProjectionGraph.targetGenerators i) := by
  have h0 : frame.top (closureGenerators row74Generators 0)=Row74OriginalSixPairFrame.rotation := top_generator 0
  have h1 : frame.top (closureGenerators row74Generators 1)=swap := top_generator 1
  have ht0 : (closureGenerators row74Generators 0 : Equiv.Perm (Fin 12))=row74Generators 0 := rfl
  have ht1 : (closureGenerators row74Generators 1 : Equiv.Perm (Fin 12))=row74Generators 1 := rfl
  fin_cases i <;>
    simp [paired,generators,Row74PairProjectionGraph.sourceGenerators,
      Row74PairProjectionGraph.targetGenerators,map_inv,h0,h1,ht0,ht1,original]

theorem top_injective : Function.Injective frame.top :=
  Row74PairProjectionGraph.certificate.first_comp_injective_of_generated
    paired paired_injective generators generators_full generator_binding

def topEquiv : row74Interface.top ≃* frame.top.range :=
  MulEquiv.ofBijective frame.top.rangeRestrict
    ⟨fun _ _ h => top_injective (congrArg Subtype.val h),frame.top.rangeRestrict_surjective⟩
end SymmetricSubgroupAsymptotics.Row74OriginalFaithfulPairTop
