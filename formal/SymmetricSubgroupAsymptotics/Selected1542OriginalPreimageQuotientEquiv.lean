import SymmetricSubgroupAsymptotics.Selected1542ActualQuotientGraph
import SymmetricSubgroupAsymptotics.Selected1542TargetQuartetFrame

/-! The selected graph covers the whole quotient of the original generated
group. The target is the literal generated twelve-point permutation group. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Selected1542QuotientStructure

local instance : Fintype originalPreimage := Fintype.ofFinite _
local instance : originalPreimage.subtype.range.Normal := by
  rw [Subgroup.range_subtype]
  infer_instance

theorem graph_target_top : actualQuotientGraph.certificate.Target=⊤ := by
  change Subgroup.closure
    (Set.range (fun j => QuotientGroup.mk' originalPreimage.subtype.range (source j)))=⊤
  rw [Set.range_comp',← MonoidHom.map_closure,source_generates,← MonoidHom.range_eq_map]
  exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)

def originalQuotientEquiv :
    (Original ⧸ originalPreimage.subtype.range) ≃* literalTarget :=
  ((Subgroup.topEquiv).symm.trans
    (MulEquiv.subgroupCongr graph_target_top).symm).trans selectedQuotientEquivalence.symm

/-- An actual map on the original sixteen-point group, with the displayed
original denominator as its exact kernel. -/
def originalToTarget : Original →* literalTarget :=
  originalQuotientEquiv.toMonoidHom.comp (QuotientGroup.mk' originalPreimage.subtype.range)

theorem originalToTarget_surjective : Function.Surjective originalToTarget :=
  originalQuotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _)

theorem originalToTarget_ker : originalToTarget.ker=originalPreimage := by
  ext g
  change originalQuotientEquiv (QuotientGroup.mk' originalPreimage.subtype.range g)=1 ↔
    g ∈ originalPreimage
  rw [originalQuotientEquiv.map_eq_one_iff]
  change (g : Original ⧸ originalPreimage.subtype.range)=1 ↔ g∈originalPreimage
  rw [QuotientGroup.eq_one_iff,Subgroup.range_subtype]

end SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
