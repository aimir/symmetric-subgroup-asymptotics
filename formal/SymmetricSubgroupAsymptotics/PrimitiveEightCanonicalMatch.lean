import SymmetricSubgroupAsymptotics.PrimitiveAffineEightImprimitiveFilter
import SymmetricSubgroupAsymptotics.PrimitivePGroupDegree

/-! Primitive degree-eight actions select one of the last seven entries
of the fixed canonical catalogue. The point relabelling and conjugator
are retained; the seventeen exclusions are proved in the imported file. -/

set_option autoImplicit false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeEightCanonicalCatalogue

structure PrimitiveLiteralMatch {X : Type} (S : Subgroup (Equiv.Perm X)) where
  index : Fin 24
  primitive_index : 17 ≤ index.val
  points : X ≃ Fin 8
  conjugator : Equiv.Perm (Fin 8)
  matched : MulAut.conj conjugator • relabelSubgroup points S =
    (DegreeTwoPairedEightSharedTops.interface index).top

noncomputable def PrimitiveLiteralMatch.groupEquiv
    {X : Type} {S : Subgroup (Equiv.Perm X)} (M : PrimitiveLiteralMatch S) :
    S ≃* (DegreeTwoPairedEightSharedTops.interface M.index).top :=
  PermutationStabilizerTransport.groupEquiv S _ M.points M.conjugator M.matched

noncomputable def primitiveLiteralMatch (published : PublishedClassification)
    {X : Type} [Finite X] (S : Subgroup (Equiv.Perm X))
    [MulAction.IsPreprimitive S X] (hX : Nat.card X = 8) :
    PrimitiveLiteralMatch S := by
  let points : X ≃ Fin 8 := Finite.equivFinOfCardEq hX
  let T := relabelSubgroup points S
  have htrans : PermutationSubgroupTransitive T := by
    intro x y
    obtain ⟨g, hxy⟩ := MulAction.exists_smul_eq S (points.symm x) (points.symm y)
    refine ⟨points.permCongr g.1, ?_, ?_⟩
    · exact ⟨g.1, g.2, rfl⟩
    · change points (g.1 (points.symm x)) = y
      change g.1 (points.symm x) = points.symm y at hxy
      rw [hxy, points.apply_symm_apply]
  have hnonbinary : ¬ IsPGroup 2 T := by
    intro hT
    exact primitive_eight_not_binary hX
      (hT.of_equiv (points.permCongrHom.subgroupMap S).symm)
  let selected := originalClassification published T htrans hnonbinary
  let j : Fin 24 := Classical.choose selected
  let selectedConjugator := Classical.choose_spec selected
  let g : Equiv.Perm (Fin 8) := Classical.choose selectedConjugator
  have hg : MulAut.conj g • relabelSubgroup points S =
      (DegreeTwoPairedEightSharedTops.interface j).top :=
    Classical.choose_spec selectedConjugator
  let e := PermutationStabilizerTransport.groupEquiv S
    (DegreeTwoPairedEightSharedTops.interface j).top points g hg
  let c := PermutationStabilizerTransport.pointEquiv points g
  let f : MulActionHom e X (Fin 8) := {
    toFun := c
    map_smul' := by
      intro s x
      exact (PermutationStabilizerTransport.groupEquiv_action S
        (DegreeTwoPairedEightSharedTops.interface j).top points g hg s x).symm }
  letI : MulAction.IsPreprimitive
      (DegreeTwoPairedEightSharedTops.interface j).top (Fin 8) :=
    MulAction.IsPreprimitive.of_surjective (f := f) c.surjective
  exact {
    index := j
    primitive_index := PrimitiveAffineEightImprimitiveFilter.primitive_index_ge j
    points := points
    conjugator := g
    matched := hg }

end DegreeEightCanonicalCatalogue
end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
