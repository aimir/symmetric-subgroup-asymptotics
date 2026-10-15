import SymmetricSubgroupAsymptotics.PrimitiveAffineEightCanonicalCatalogue
import SymmetricSubgroupAsymptotics.PermutationStabilizerTransport

/-! Exact canonical matching for an arbitrary original eight-point action.
This includes the actual range on pair labels, rather than only an affine
profile's block top. The fixed canonical catalogue is the sole published
classification input. -/

set_option autoImplicit false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeEightCanonicalCatalogue

structure TransitiveLiteralMatch {X : Type} (S : Subgroup (Equiv.Perm X)) where
  index : Fin 24
  points : X ≃ Fin 8
  conjugator : Equiv.Perm (Fin 8)
  matched : MulAut.conj conjugator • relabelSubgroup points S =
    (DegreeTwoPairedEightSharedTops.interface index).top

noncomputable def transitiveLiteralMatch (published : PublishedClassification)
    {X : Type} [Finite X] (S : Subgroup (Equiv.Perm X))
    [MulAction.IsPretransitive S X] (hX : Nat.card X = 8)
    (hnonbinary : ¬ IsPGroup 2 S) : TransitiveLiteralMatch S := by
  let points : X ≃ Fin 8 := Finite.equivFinOfCardEq hX
  let T := relabelSubgroup points S
  have ht : PermutationSubgroupTransitive T := by
    intro x y
    obtain ⟨g, hxy⟩ := MulAction.exists_smul_eq S (points.symm x) (points.symm y)
    refine ⟨points.permCongr g.1, ⟨g.1, g.2, rfl⟩, ?_⟩
    change points (g.1 (points.symm x)) = y
    change g.1 (points.symm x) = points.symm y at hxy
    rw [hxy, points.apply_symm_apply]
  have hT : ¬ IsPGroup 2 T := by
    intro h
    exact hnonbinary (h.of_equiv (points.permCongrHom.subgroupMap S).symm)
  let selected := originalClassification published T ht hT
  let j := Classical.choose selected
  let selectedConjugator := Classical.choose_spec selected
  exact {
    index := j
    points := points
    conjugator := Classical.choose selectedConjugator
    matched := Classical.choose_spec selectedConjugator }

end DegreeEightCanonicalCatalogue
end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
