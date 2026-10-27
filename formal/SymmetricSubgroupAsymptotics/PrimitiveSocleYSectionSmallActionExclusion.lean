import SymmetricSubgroupAsymptotics.CFSGYE6ActualNormalizerIndex
import SymmetricSubgroupAsymptotics.PrimitiveSocleYSectionOrdinaryTail
import SymmetricSubgroupAsymptotics.PrimitiveSocleLeastIndexDegreeComparison
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! Actual original nonaffine Y sections have degree at least27. The
same simple group and actual isomorphism are retained throughout; no
model-order, generation, numerical or small-action callback is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleYSectionSmallActionExclusion
open PrimitiveSocleRawStructure CFSGReduction
open PrimitiveSocleYSectionOrdinaryTail

private theorem section_least_index (arms : CFSG.Models.YGroups.Arms)
    [Finite (CFSG.Models.YGroups.SimpleSection arms)]
    [IsSimpleGroup (CFSG.Models.YGroups.SimpleSection arms)]
    (hn : ¬IsMulCommutative (CFSG.Models.YGroups.SimpleSection arms))
    (ell : ℕ) (hell : LeastProperIndex (CFSG.Models.YGroups.SimpleSection arms) ell) :
    27≤ell := by
  obtain ⟨H,hH,he⟩ := hell.1
  rw [←he]
  exact CFSGYE6ActualNormalizerIndex.proper_index_ge_twentySeven arms hn H hH

theorem model_least_index_ge_twentySeven (s : CFSG.Sporadic) (hs : IsYSectionModel s)
    [hfinite : Finite s.Model] [hsimple : IsSimpleGroup s.Model] (hn : ¬IsMulCommutative s.Model)
    (ell : ℕ) (hell : LeastProperIndex s.Model ell) : 27≤ell := by
  cases s <;> try exact False.elim hs
  case fi22 => exact @section_least_index CFSG.Models.YGroups.arms332 hfinite hsimple hn ell hell
  case fi23 => exact @section_least_index CFSG.Models.YGroups.arms432 hfinite hsimple hn ell hell
  case fi24Prime => exact @section_least_index CFSG.Models.YGroups.arms442 hfinite hsimple hn ell hell
  case babyMonster => exact @section_least_index CFSG.Models.YGroups.arms433 hfinite hsimple hn ell hell

theorem degree_ge_twentySeven
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X) (s : CFSG.Sporadic) (hs : IsYSectionModel s)
    (e : D.Simple ≃* s.Model) : 27≤Nat.card X := by
  letI : Finite s.Model := Finite.of_equiv D.Simple e.toEquiv
  letI : IsSimpleGroup s.Model := e.symm.isSimpleGroup
  have hn : ¬IsMulCommutative s.Model := fun hc =>
    D.noncommutative ((isMulCommutative_congr e).mpr hc)
  obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
  exact (model_least_index_ge_twentySeven s hs hn ell
    (leastProperIndex_of_mulEquiv e ell hell)).trans
    (PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell)

theorem not_y_section_of_degree_lt_twentySeven
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X) (s : CFSG.Sporadic)
    (e : D.Simple ≃* s.Model) (hdegree : Nat.card X<27) : ¬IsYSectionModel s := by
  intro hs
  exact (not_lt_of_ge (degree_ge_twentySeven D s hs e)) hdegree

end SymmetricSubgroupAsymptotics.PrimitiveSocleYSectionSmallActionExclusion
