import SymmetricSubgroupAsymptotics.PrimitiveSocleDirectProduct

/-! The FULL socle of a faithful finite primitive action is either affine,
or a homogeneous nonabelian simple power. The two-minimal-normal regular
case already supplies its exact diagonal degree form. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleONanScottHelpers

structure PrimitiveFullSocleChart (G X : Type) [Group G] [Finite G]
    [Finite X] [MulAction G X]
    extends HomogeneousNonabelianChart (finiteGroupSocle G) where
  transitive : MulAction.IsPretransitive (finiteGroupSocle G) X
  degreeOrMinimal :
    IsMinimalNormalSubgroup (finiteGroupSocle G) ∨
    (∃ a : ℕ, factorCount ≤ 2*a ∧ Nat.card X=Nat.card Simple ^ a)

/-- The primitive full-socle algebraic alternative. The one remaining
minimal-socle branch will use the actual point-stabilizer Scott theorem. -/
theorem fullSocle_or_affine_nonempty
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X] :
    Nonempty (PrimitiveFullSocleChart G X ⊕ PrimitiveAffineProfile G X) := by
  have hGnt : Nontrivial G := by
    rcases subsingleton_or_nontrivial G with h|h
    · letI : Subsingleton G := h
      obtain ⟨x,y,hxy⟩ := exists_pair_ne X
      obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G x y
      exact False.elim (hxy (by simpa only [Subsingleton.elim g 1,one_smul] using hg))
    · exact h
  letI : Nontrivial G := hGnt
  obtain ⟨E,hE⟩ := exists_minimalNormal (G := G)
  by_cases hcomm : IsMulCommutative E
  · exact ⟨.inr (Classical.choice (affineProfile_of_abelian_minimal_nonempty E hE hcomm))⟩
  letI : E.Normal := hE.1
  obtain ⟨A⟩ := chart_of_minimalNormal_nonempty E hE hcomm
  let C : Subgroup G := Subgroup.centralizer (E : Set G)
  have htrans : MulAction.IsPretransitive (finiteGroupSocle G) X := full_socle_transitive (X := X) E hE
  by_cases hc : C=⊥
  · have hs : finiteGroupSocle G=E := full_socle_eq_of_centralizer_bot E hE hc
    let D : HomogeneousNonabelianChart (finiteGroupSocle G) :=
      A.transport (MulEquiv.subgroupCongr hs.symm)
    exact ⟨.inl {
      toHomogeneousNonabelianChart := D
      transitive := htrans
      degreeOrMinimal := Or.inl (by simpa only [hs] using hE) }⟩
  · obtain ⟨hC,hdis,hs,hregularE,hregularC⟩ := centralizer_regular_alternative (X := X) E hE hcomm hc
    have hcommEC : ∀ e : E, ∀ c : C, Commute (e : G) (c : G) := by
      intro e c
      exact Subgroup.mem_centralizer_iff.mp c.property (e : G) e.property
    let x : X := Classical.choice inferInstance
    let eEC : E ≃* C := commutingRegularEquiv E C hregularE hregularC hcommEC x
    let eS : (finiteGroupSocle G) ≃* (E×E) :=
      (MulEquiv.subgroupCongr hs).trans
        ((commutingDisjointSupEquiv E C hdis hcommEC).symm.trans
          ((MulEquiv.refl E).prodCongr eEC.symm))
    let D : HomogeneousNonabelianChart (finiteGroupSocle G) := A.square.transport eS.symm
    have hdegree : Nat.card X=Nat.card A.Simple ^ A.factorCount :=
      (Nat.card_congr (regularPointEquiv E hregularE x)).symm.trans A.cardinality
    exact ⟨.inl {
      toHomogeneousNonabelianChart := D
      transitive := htrans
      degreeOrMinimal := Or.inr ⟨A.factorCount,by
        change A.factorCount+A.factorCount ≤ 2*A.factorCount
        omega,hdegree⟩ }⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleONanScottHelpers
