import SymmetricSubgroupAsymptotics.CFSGMonsterRemoteTailIndex
import SymmetricSubgroupAsymptotics.PrimitiveSocleLeastIndexDegreeComparison
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport
import SymmetricSubgroupAsymptotics.OriginalMinimalBlock

/-! The actual original Monster factor has degree at least33, by its
actual perfect E6 image and two independent commuting ternary tails.
This retains the same D, original simple-factor equivalence and actual
block fibre; no whole-generation or finite-order formula is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleMonsterRemoteTailDegree
open PrimitiveSocleRawStructure CFSGReduction

 theorem model_least_index_ge_thirtyThree
    [Finite CFSG.Models.Monster] [IsSimpleGroup CFSG.Models.Monster]
    (hn : ¬IsMulCommutative CFSG.Models.Monster) (ell : ℕ)
    (hell : LeastProperIndex CFSG.Models.Monster ell) : 33≤ell := by
  obtain ⟨H,hH,he⟩ := hell.1
  rw [←he]
  exact CFSGMonsterRemoteTailIndex.proper_index_ge_thirtyThree hn H hH

 theorem degree_ge_thirtyThree
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X) (e : D.Simple ≃* CFSG.Models.Monster) : 33≤Nat.card X := by
  letI : Finite CFSG.Models.Monster := Finite.of_equiv D.Simple e.toEquiv
  letI : IsSimpleGroup CFSG.Models.Monster := e.symm.isSimpleGroup
  have hn : ¬IsMulCommutative CFSG.Models.Monster := fun hc =>
    D.noncommutative ((isMulCommutative_congr e).mpr hc)
  obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
  exact (model_least_index_ge_thirtyThree hn ell (leastProperIndex_of_mulEquiv e ell hell)).trans
    (PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell)

 theorem not_monster_of_degree_lt_thirtyThree
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X) (e : D.Simple ≃* CFSG.Models.Monster)
    (hdegree : Nat.card X<33) : False :=
  (not_lt_of_ge (degree_ge_thirtyThree D e)) hdegree

 theorem original_block_not_monster_of_fibre_lt_thirtyThree
    {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀)
    (D : NonaffineData block.Component block.Fibre)
    (e : D.Simple ≃* CFSG.Models.Monster) (hdegree : Nat.card block.Fibre<33) : False :=
  not_monster_of_degree_lt_thirtyThree D e hdegree

end SymmetricSubgroupAsymptotics.PrimitiveSocleMonsterRemoteTailDegree
