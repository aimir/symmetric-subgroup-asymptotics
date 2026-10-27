import SymmetricSubgroupAsymptotics.CFSGMonsterE6ActualNormalizerIndex
import SymmetricSubgroupAsymptotics.PrimitiveSocleLeastIndexDegreeComparison
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport
import SymmetricSubgroupAsymptotics.OriginalMinimalBlock

/-! SOURCE DRAFT: depends on the final ACTUAL E6 Monster assembly, not an
assumed System or index callback. Actual nonaffine Monster simple factors
have original degree≥27. This excludes only actions of degree<27, including
original minimal-block fibres, and does not assert whole generation. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleMonsterSmallActionExclusion
open PrimitiveSocleRawStructure CFSGReduction

 theorem model_least_index_ge_twentySeven
    [Finite CFSG.Models.Monster] [IsSimpleGroup CFSG.Models.Monster]
    (hn : ¬IsMulCommutative CFSG.Models.Monster) (ell : ℕ)
    (hell : LeastProperIndex CFSG.Models.Monster ell) : 27≤ell := by
  obtain ⟨H,hH,he⟩ := hell.1
  rw [←he]
  exact CFSGMonsterE6ActualNormalizerIndex.proper_index_ge_twentySeven hn H hH

 theorem degree_ge_twentySeven
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X) (e : D.Simple ≃* CFSG.Models.Monster) : 27≤Nat.card X := by
  letI : Finite CFSG.Models.Monster := Finite.of_equiv D.Simple e.toEquiv
  letI : IsSimpleGroup CFSG.Models.Monster := e.symm.isSimpleGroup
  have hn : ¬IsMulCommutative CFSG.Models.Monster := fun hc =>
    D.noncommutative ((isMulCommutative_congr e).mpr hc)
  obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
  exact (model_least_index_ge_twentySeven hn ell (leastProperIndex_of_mulEquiv e ell hell)).trans
    (PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell)

 theorem not_monster_of_degree_lt_twentySeven
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X) (e : D.Simple ≃* CFSG.Models.Monster)
    (hdegree : Nat.card X<27) : False :=
  (not_lt_of_ge (degree_ge_twentySeven D e)) hdegree

 theorem original_block_not_monster_of_fibre_lt_twentySeven
    {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀)
    (D : NonaffineData block.Component block.Fibre)
    (e : D.Simple ≃* CFSG.Models.Monster) (hdegree : Nat.card block.Fibre<27) : False :=
  not_monster_of_degree_lt_twentySeven D e hdegree

end SymmetricSubgroupAsymptotics.PrimitiveSocleMonsterSmallActionExclusion
