import SymmetricSubgroupAsymptotics.Selected1071ActualQuotientGraph

/-! The selected graph covers the whole quotient of the original generated
group. The target is the literal generated twelve-point permutation group. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Selected1071QuotientGraph

local instance : Fintype originalKernel := Fintype.ofFinite _
local instance : originalKernel.subtype.range.Normal := by
  rw [Subgroup.range_subtype]
  infer_instance

theorem source_generates : Subgroup.closure (Set.range source)=⊤ := by
  apply Subgroup.map_injective (f := Original.subtype) Subtype.val_injective
  rw [MonoidHom.map_closure,← Set.range_comp]
  change Subgroup.closure (Set.range sourceGenerators)=
    (⊤ : Subgroup Original).map Original.subtype
  rw [← MonoidHom.range_eq_map,Subgroup.range_subtype]
  rfl

theorem graph_target_top : actualQuotientGraph.certificate.Target=⊤ := by
  change Subgroup.closure
    (Set.range (fun j => QuotientGroup.mk' originalKernel.subtype.range (source j)))=⊤
  rw [Set.range_comp',← MonoidHom.map_closure,source_generates,← MonoidHom.range_eq_map]
  exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)

def literalTarget : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range targetGenerators)

def originalQuotientEquiv :
    (Original ⧸ originalKernel.subtype.range) ≃* literalTarget :=
  ((Subgroup.topEquiv).symm.trans
    (MulEquiv.subgroupCongr graph_target_top).symm).trans selectedQuotientEquivalence.symm

/-- An actual map on the original sixteen-point group, with the displayed
original denominator as its exact kernel. -/
def originalToTarget : Original →* literalTarget :=
  originalQuotientEquiv.toMonoidHom.comp (QuotientGroup.mk' originalKernel.subtype.range)

theorem originalToTarget_surjective : Function.Surjective originalToTarget :=
  originalQuotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _)

theorem originalToTarget_ker : originalToTarget.ker=originalKernel := by
  ext g
  change originalQuotientEquiv (QuotientGroup.mk' originalKernel.subtype.range g)=1 ↔
    g ∈ originalKernel
  rw [originalQuotientEquiv.map_eq_one_iff]
  change (g : Original ⧸ originalKernel.subtype.range)=1 ↔ g∈originalKernel
  rw [QuotientGroup.eq_one_iff,Subgroup.range_subtype]

end SymmetricSubgroupAsymptotics.Selected1071QuotientGraph
