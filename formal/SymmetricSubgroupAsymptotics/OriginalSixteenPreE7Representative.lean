import SymmetricSubgroupAsymptotics.Non2PreE7NonPairPhysicalFrontier
import SymmetricSubgroupAsymptotics.BinaryConjugacyTransport

/-! A genuine preE7 non-pair representative of any original nonbinary
transitive16point action. Both excluded pair menus have widths larger than
16, so no ambient finite catalogue or locator is required. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace OriginalSixteenPreE7Representative

structure Chart (H : Subgroup (Equiv.Perm (Fin 16))) where
  index : PreE7NonPairActionClass 16
  conjugator : Equiv.Perm (Fin 16)
  point_conjugacy : MulAut.conj conjugator • H = preE7NonPairAction 16 index
  groupEquiv : H ≃* preE7NonPairAction 16 index

theorem exists_index (H : Subgroup (Equiv.Perm (Fin 16)))
    (hH : ¬ IsPGroup 2 H) (htrans : MulAction.IsPretransitive H (Fin 16)) :
    ∃ i : PreE7NonPairActionClass 16, ∃ c : Equiv.Perm (Fin 16),
      MulAut.conj c • H = preE7NonPairAction 16 i := by
  obtain ⟨i,c,hc⟩ := Non2TransitiveActionClass.representative_cover H hH htrans
  have hpre : IsPreE7ActionClass 16 i := by
    intro d hd
    have hg := d.pairCount_ge_24
    change 2*d.pairCount=16 at hd
    omega
  let j : PreE7ActionClass 16 := ⟨i,hpre⟩
  have hnonpair : IsPreE7NonPairActionClass 16 j := by
    intro d hd
    have hg := d.pairCount_ge_24
    omega
  exact ⟨⟨j,hnonpair⟩,c,hc⟩

/-- Choose only after existence of the actual point-conjugate class is proved. -/
def choose (H : Subgroup (Equiv.Perm (Fin 16)))
    (hH : ¬ IsPGroup 2 H) (htrans : MulAction.IsPretransitive H (Fin 16)) : Chart H := by
  let h := exists_index H hH htrans
  let i := Classical.choose h
  let hi := Classical.choose_spec h
  let c := Classical.choose hi
  have hc : MulAut.conj c • H = preE7NonPairAction 16 i := Classical.choose_spec hi
  exact ⟨i,c,hc,actionConjugacyEquiv c hc⟩

end OriginalSixteenPreE7Representative
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics
end
