import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveCubicQuartetB6Sources

/-! Six actual structural source rows. This partial batch supplies no
182-entry table, no distinctness assertion, and no global coverage locator. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineDegreeTwoSixPairCubicQuartetSourceBatch
open PrimitiveAffineDegreeTwoTwelveCubicQuartetB6Sources
open PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwelvePairFiniteCatalogue

def originals : Fin 6 → Subgroup (Equiv.Perm (Fin 12)) :=
  ![Row6Top,Row7Top,Row25Top,Row26Top,Row56Top,Row90Top]

def representatives (hKP : KovacsPraegerAbelianizationBound) : Fin 6 → PreE7PairActionClass 6 :=
  ![Row6.representative hKP,Row7.representative hKP,Row25.representative hKP,Row26.representative hKP,Row56.representative hKP,Row90.representative hKP]

def sources (hKP : KovacsPraegerAbelianizationBound) (i : Fin 6) :
    PreE7B6SourceData 12 (preE7SixPairNonPairAction (representatives hKP i)) := by
  apply Classical.choice
  change Nonempty (PreE7B6SourceData 12
    (preE7SixPairNonPairAction (representatives hKP i)))
  fin_cases i
  · exact ⟨Row6.source hKP⟩
  · exact ⟨Row7.source hKP⟩
  · exact ⟨Row25.source hKP⟩
  · exact ⟨Row26.source hKP⟩
  · exact ⟨Row56.source hKP⟩
  · exact ⟨Row90.source hKP⟩

theorem actual_correspondence (hKP : KovacsPraegerAbelianizationBound) (i : Fin 6) :
    ∃ c : Equiv.Perm (Fin 12), relabelSubgroup c (originals i) =
      preE7PairAction 6 (representatives hKP i) := by
  fin_cases i
  · have h := Classical.choose_spec (Row6.exists_source hKP)
    exact ⟨Classical.choose h,(Classical.choose_spec h).1⟩
  · have h := Classical.choose_spec (Row7.exists_source hKP)
    exact ⟨Classical.choose h,(Classical.choose_spec h).1⟩
  · have h := Classical.choose_spec (Row25.exists_source hKP)
    exact ⟨Classical.choose h,(Classical.choose_spec h).1⟩
  · have h := Classical.choose_spec (Row26.exists_source hKP)
    exact ⟨Classical.choose h,(Classical.choose_spec h).1⟩
  · have h := Classical.choose_spec (Row56.exists_source hKP)
    exact ⟨Classical.choose h,(Classical.choose_spec h).1⟩
  · have h := Classical.choose_spec (Row90.exists_source hKP)
    exact ⟨Classical.choose h,(Classical.choose_spec h).1⟩

end PrimitiveAffineDegreeTwoSixPairCubicQuartetSourceBatch
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics
end
