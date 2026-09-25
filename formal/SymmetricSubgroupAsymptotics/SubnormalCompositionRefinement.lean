import SymmetricSubgroupAsymptotics.NormalChiefSeries
import SymmetricSubgroupAsymptotics.MaximalNormalQuotient
import Mathlib.GroupTheory.IsSubnormal
import Mathlib.Order.RelSeries

/-! Genuine composition refinements of original finite chief chains.
The finite poset contains literal subnormal subgroups. Its covers are
proved to be normal inclusions with simple quotient, so refining a chief
chain there constructs an actual composition series without assuming a
Jordan–Hölder instance or composition-count invariance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics

abbrev SubnormalPoint (R:Type) [Group R] := {K:Subgroup R // K.IsSubnormal}

section Cover
variable {R:Type} [Group R] (B L:SubnormalPoint R) (hc:B⋖L)
include hc

theorem subnormalCover_maximal_normal :
    (B.val.subgroupOf L.val).Normal ∧ B.val.subgroupOf L.val≠⊤ ∧
      ∀M:Subgroup L.val,M.Normal → B.val.subgroupOf L.val≤M →
        M=B.val.subgroupOf L.val ∨ M=⊤ := by
  have hBL : B.val≤L.val := hc.le
  have hne : B.val.subgroupOf L.val≠⊤ := by
    intro he
    exact (not_le_of_gt hc.1) (Subgroup.subgroupOf_eq_top.mp he)
  have hproper (M:Subgroup L.val) (hM:M.Normal) (hlo:B.val.subgroupOf L.val≤M)
      (hneM:M≠⊤) : M=B.val.subgroupOf L.val := by
    let T : SubnormalPoint R := ⟨M.map L.val.subtype,hM.isSubnormal.trans' L.property⟩
    have hlo' : B≤T := by
      have h := Subgroup.map_mono (f:=L.val.subtype) hlo
      rwa [Subgroup.map_subgroupOf_eq_of_le hBL] at h
    have hhi' : T≤L := Subgroup.map_subtype_le M
    rcases hc.eq_or_eq hlo' hhi' with h|h
    · apply Subgroup.map_injective L.val.subtype_injective
      simpa only [Subgroup.map_subgroupOf_eq_of_le hBL] using congrArg Subtype.val h
    · exfalso
      apply hneM
      apply Subgroup.map_injective L.val.subtype_injective
      simpa only [←MonoidHom.range_eq_map,Subgroup.range_subtype] using congrArg Subtype.val h
  have hn : (B.val.subgroupOf L.val).Normal := by
    obtain ⟨M,hM,hlo,hlt⟩ :=
      (B.property.subgroupOf (K:=L.val)).exists_normal_and_le_and_lt_top_of_ne hne
    have he := hproper M hM hlo hlt.ne
    exact he ▸ hM
  refine ⟨hn,hne,?_⟩
  intro M hM hlo
  by_cases he:M=⊤
  · exact Or.inr he
  · exact Or.inl (hproper M hM hlo he)

theorem subnormalCover_quotient_simple :
    ∃ hn:(B.val.subgroupOf L.val).Normal,
      @IsSimpleGroup (L.val⧸B.val.subgroupOf L.val)
        (@QuotientGroup.Quotient.group L.val inferInstance (B.val.subgroupOf L.val) hn) := by
  obtain ⟨hn,hne,hmax⟩ := subnormalCover_maximal_normal B L hc
  letI := hn
  exact ⟨hn,maximal_normal_quotient_simple L.val (B.val.subgroupOf L.val) hne hmax⟩

end Cover

structure SubnormalCompositionSeries (R:Type) [Group R] where
  chain : RelSeries {(B,L):SubnormalPoint R×SubnormalPoint R | B⋖L}
  head : chain.head.val=⊥
  last : chain.last.val=⊤

/-- Every original chief subgroup occurs literally in this genuine
composition series. No abstract group replacement or unproved refinement
hypothesis is introduced. -/
theorem actualChiefSeries_composition_refinement {R:Type} [Group R] [Finite R]
    (s:ActualChiefSeries R) :
    ∃ t:SubnormalCompositionSeries R,
      ∃i:Fin (s.length+1)↪Fin (t.chain.length+1),
        (∀j,(t.chain (i j)).val=s.subgroup j) ∧
          i 0=0 ∧ i (Fin.last s.length)=Fin.last t.chain.length := by
  let c : LTSeries (SubnormalPoint R) := {
    length := s.length
    toFun := fun i=>⟨s.subgroup i,(s.normal i).isSubnormal⟩
    step := fun i=>s.step i }
  obtain ⟨t,i,he,h0,hl⟩ := c.exists_relSeries_covBy
  have ht0 : t.head.val=⊥ := by
    calc
      t.head.val=(t (i 0)).val := congrArg (fun j=>(t j).val) h0.symm
      _=s.subgroup 0 := congrArg Subtype.val (congrFun he 0)
      _=⊥ := s.head
  have htl : t.last.val=⊤ := by
    calc
      t.last.val=(t (i (Fin.last s.length))).val :=
        congrArg (fun j=>(t j).val) hl.symm
      _=s.subgroup (Fin.last s.length) := congrArg Subtype.val (congrFun he _)
      _=⊤ := s.last
  refine ⟨⟨t,ht0,htl⟩,i,?_,h0,hl⟩
  intro j
  exact congrArg Subtype.val (congrFun he j)

end SymmetricSubgroupAsymptotics
