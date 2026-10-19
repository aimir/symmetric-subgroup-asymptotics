import SymmetricSubgroupAsymptotics.MarkedC4GeneratorNumbers

/-! Mark-zero derived normal subgroups retain their ordinary normal rank.
The marker is abelian and global. Injectivity on each relevant normal
subgroup is DERIVED from its trivial marker and physical coordinates. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualMarkZeroNormalRank

theorem normalGen_map_eq {G L : Type} [Group G] [Finite G] [Group L] [Finite L]
    (π : G →* L) (hπ : Function.Surjective π) (U : Subgroup G) [U.Normal]
    (hker : ∀ x∈U,π x=1 → x=1) : normalGen (U.map π)=normalGen U := by
  letI : (U.map π).Normal := Subgroup.Normal.map inferInstance π hπ
  apply le_antisymm (normalGen_map_le π hπ U)
  obtain ⟨S,hS,hs,hcl⟩ := normalGen_spec (U.map π)
  obtain ⟨T,hT,ht,hgen⟩ := exists_layer_lift π hπ ⊥ U
    (fun x hx he => Subgroup.mem_bot.mpr (hker x hx he)) S hs hcl
  have hc : Subgroup.normalClosure (T : Set G)=U := by
    apply le_antisymm (Subgroup.normalClosure_le_normal ht)
    simpa only [sup_bot_eq] using hgen
  exact (normalGen_le ht hc).trans (hT.trans_eq hS)

variable {B M : Type} [Group B] [Finite B] [CommGroup M] [Finite M]
  (A : Subgroup (B × M))
def physical : A →* B := (MonoidHom.fst B M).comp A.subtype
def mark : A →* M := (MonoidHom.snd B M).comp A.subtype
abbrev PhysicalImage := (physical A).range
def projection : A →* PhysicalImage A := (physical A).rangeRestrict

/-- The derived subgroup has marker equal to one because the SINGLE
global marking group is abelian. -/
theorem derived_mark_zero : commutator A≤(mark A).ker :=
  Abelianization.commutator_subset_ker (mark A)

/-- On every normal subgroup in the derived source, deleting the marker
preserves the actual ambient normal-generator number exactly. -/
theorem derived_normal_rank_eq (U : Subgroup A) [U.Normal]
    (hU : U≤commutator A) :
    normalGen (U.map (projection A))=normalGen U := by
  apply normalGen_map_eq (projection A) (physical A).rangeRestrict_surjective U
  intro x hx he
  have hp : x.val.1=1 := congrArg Subtype.val he
  have hm : x.val.2=1 := derived_mark_zero A (hU hx)
  exact Subtype.ext (Prod.ext hp hm)

end SymmetricSubgroupAsymptotics.MarkedC4.ActualMarkZeroNormalRank
