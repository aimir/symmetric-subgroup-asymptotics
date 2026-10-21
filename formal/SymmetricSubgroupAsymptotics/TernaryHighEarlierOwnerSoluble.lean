import SymmetricSubgroupAsymptotics.TernaryHighOwnerCapacity
import SymmetricSubgroupAsymptotics.LinearThreeSolvable
import SymmetricSubgroupAsymptotics.PrimitiveAffineHeadOrderBudget
import SymmetricSubgroupAsymptotics.PrimitiveSmallSocleSingleFactor
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawOneFactor
import SymmetricSubgroupAsymptotics.SemisimpleNormalIntersectionPerfect
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawONanScottProof
import Mathlib.GroupTheory.Nilpotent

/-! Each original intrinsic high-ternary owner is soluble. Therefore an
actual primitive degree12 pair in the new nonaffine sector cannot belong to
an earlier intrinsic owner. This keeps the old owner continuation on its
original imprimitive degree12 geometry. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

private theorem pgroup_soluble {G : Type} [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (h : IsPGroup p G) : IsSolvable G := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Group.IsNilpotent G := h.isNilpotent
  infer_instance

private theorem extension_soluble {G : Type} [Group G]
    (N : Subgroup G) [N.Normal] [IsSolvable N] [IsSolvable (G⧸N)] :
    IsSolvable G :=
  solvable_of_ker_le_range N.subtype (QuotientGroup.mk' N)
    (by rw [QuotientGroup.ker_mk',Subgroup.range_subtype])

/-- The six older intrinsic owners are all soluble on the original group. -/
theorem TernaryHighEarlierOwner.isSolvable
    {A X : Type} [Group A] [Finite A] [MulAction A X] [FaithfulSMul A X]
    (h : TernaryHighEarlierOwner A X) : IsSolvable A := by
  rcases h with hP|hA4|hOdd|hCyclic|hPrime|hNine
  · exact pgroup_soluble 3 Nat.prime_three hP
  · obtain ⟨e,he⟩ := hA4
    letI : IsSolvable (Equiv.Perm (Fin 4)) := naturalS4_isSolvable
    exact solvable_of_solvable_injective (f := labelledActionHom e) (labelledActionHom_injective e)
  · obtain ⟨W⟩ := hOdd
    letI : W.ternary.Normal := W.normal
    letI : IsSolvable W.ternary := pgroup_soluble 3 Nat.prime_three W.ternaryPGroup
    have hc : Nat.card (A⧸W.ternary)=2 := by
      rw [←Subgroup.index_eq_card,W.index_two]
    letI : IsCyclic (A⧸W.ternary) := isCyclic_of_prime_card hc
    letI : CommGroup (A⧸W.ternary) := IsCyclic.commGroup
    exact extension_soluble W.ternary
  · obtain ⟨W⟩ := hCyclic
    letI : W.base.Normal := W.base_normal
    letI : IsSolvable W.base := pgroup_soluble 2 Nat.prime_two W.basePGroup
    letI : IsSolvable W.complement := pgroup_soluble 3 Nat.prime_three W.complementPGroup
    let f : W.complement→*(A⧸W.base) := (QuotientGroup.mk' W.base).comp W.complement.subtype
    have hf : Function.Surjective f := by
      intro q
      obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective W.base q
      refine ⟨W.factorComplement g,?_⟩
      have hh := congrArg (QuotientGroup.mk' W.base) (W.factorization g)
      have hb : (QuotientGroup.mk' W.base) (W.factorBase g : A) = 1 :=
        (QuotientGroup.eq_one_iff (W.factorBase g : A)).mpr (W.factorBase g).property
      rw [map_mul, hb, one_mul] at hh
      exact hh
    letI : IsSolvable (A⧸W.base) := solvable_of_surjective (f := f) hf
    exact extension_soluble W.base
  · obtain ⟨W⟩ := hPrime
    letI : IsSolvable (Equiv.Perm (Fin 4)) := naturalS4_isSolvable
    letI : IsSolvable W.top.ker :=
      solvable_of_solvable_injective (f := W.coordinates) W.coordinates_injective
    exact solvable_of_ker_le_range W.top.ker.subtype W.top (by rw [Subgroup.range_subtype])
  · obtain ⟨W⟩ := hNine
    letI : IsSolvable W.base := pgroup_soluble 2 Nat.prime_two W.base_isPGroup
    letI : IsSolvable (A⧸W.base) := pgroup_soluble 3 Nat.prime_three W.quotient_three_group
    exact extension_soluble W.base

/-- An older high owner of degree12 is actually imprimitive. No false
strict-head inequality is asserted for arbitrary primitive degree12. -/
theorem TernaryHighEarlierOwner.degreeTwelve_imprimitive
    {A X : Type} [Group A] [Finite A] [Finite X] [MulAction A X]
    [FaithfulSMul A X] (h : TernaryHighEarlierOwner A X)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (h12 : Nat.card X=12) : ¬MulAction.IsPreprimitive A X := by
  intro hp
  letI : MulAction.IsPreprimitive A X := hp
  letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  letI : IsSolvable A := h.isSolvable
  cases Classical.choice (PrimitiveSocleRawStructure.publishedONanScottStructure A X) with
  | inr P =>
      have hh := P.degree_isPrimePow hp
      rw [h12] at hh
      exact (show ¬IsPrimePow (12 : ℕ) by decide) hh
  | inl D =>
      have hk := D.factorCount_one_of_degree_lt_twentyFive hindex (by omega)
      letI : IsSimpleGroup (finiteGroupSocle A) := (D.oneFactorEquiv hk).isSimpleGroup
      letI : Group.IsPerfect (finiteGroupSocle A) :=
        Group.IsPerfect.top_iff.mp (D.chart.normal_subgroup_perfect ⊤)
      exact Group.IsPerfect.not_isSolvable (finiteGroupSocle A) inferInstance

end SymmetricSubgroupAsymptotics
