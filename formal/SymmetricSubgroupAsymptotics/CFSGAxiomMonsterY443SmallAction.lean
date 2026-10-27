import SymmetricSubgroupAsymptotics.CFSGAxiomMonsterY443BinaryFacts
import SymmetricSubgroupAsymptotics.PrimitiveSocleYSectionSmallActionExclusion

/-! Small-action exclusion for the actual raw-derived Axiom69 Y443 carrier.
Inherited simplicity makes its full centre trivial, so the checked literal
Y-section index theorem applies through a genuine quotient equivalence.
No old Y555 Monster identification or classification assumption is used.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGAxiomMonsterY443SmallAction
open CFSG.Models.YGroups CFSGReduction PrimitiveSocleRawStructure
open CFSGAxiomMonsterY443ElevenGenerators CFSGAxiomMonsterY443BinaryFacts

theorem derived_center_eq_bot [IsSimpleGroup MonsterY443Derived]
    (hn : ¬IsMulCommutative MonsterY443Derived) :
    Subgroup.center (commutator (CFSG.Models.YGroups.Group arms443))=⊥ := by
  letI : IsSimpleGroup (commutator (CFSG.Models.YGroups.Group arms443)) :=
    derivedMulEquiv.symm.isSimpleGroup
  have hnon : ¬IsMulCommutative (commutator (CFSG.Models.YGroups.Group arms443)) :=
    fun hc => hn ((isMulCommutative_congr derivedMulEquiv).mpr hc)
  rcases (inferInstance :
    (Subgroup.center (commutator (CFSG.Models.YGroups.Group arms443))).Normal).eq_bot_or_eq_top
      with h | h
  · exact h
  · exact (hnon (Subgroup.center_eq_top_iff.mp h)).elim

def sectionMulEquiv [IsSimpleGroup MonsterY443Derived]
    (hn : ¬IsMulCommutative MonsterY443Derived) :
    MonsterY443Derived≃*SimpleSection arms443 :=
  derivedMulEquiv.trans
    ((QuotientGroup.quotientMulEquivOfEq (derived_center_eq_bot hn)).trans
      QuotientGroup.quotientBot).symm

theorem least_index_ge_twentySeven [Finite MonsterY443Derived]
    [IsSimpleGroup MonsterY443Derived] (hn : ¬IsMulCommutative MonsterY443Derived)
    (ell : ℕ) (hell : LeastProperIndex MonsterY443Derived ell) : 27≤ell := by
  let e := sectionMulEquiv hn
  letI : Finite (SimpleSection arms443) := Finite.of_equiv MonsterY443Derived e.toEquiv
  letI : IsSimpleGroup (SimpleSection arms443) := e.symm.isSimpleGroup
  have hnon : ¬IsMulCommutative (SimpleSection arms443) :=
    fun hc => hn ((isMulCommutative_congr e).mpr hc)
  have hs := leastProperIndex_of_mulEquiv e ell hell
  obtain ⟨H,hH,he⟩ := hs.1
  rw [←he]
  exact CFSGYE6ActualNormalizerIndex.proper_index_ge_twentySeven arms443 hnon H hH

theorem degree_ge_twentySeven
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X) (e : D.Simple≃*MonsterY443Derived) : 27≤Nat.card X := by
  letI : Finite MonsterY443Derived := Finite.of_equiv D.Simple e.toEquiv
  letI : IsSimpleGroup MonsterY443Derived := e.symm.isSimpleGroup
  have hn : ¬IsMulCommutative MonsterY443Derived :=
    fun hc => D.noncommutative ((isMulCommutative_congr e).mpr hc)
  obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
  exact (least_index_ge_twentySeven hn ell (leastProperIndex_of_mulEquiv e ell hell)).trans
    (PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell)

theorem not_model_of_degree_lt_twentySeven
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X) (hn : Nat.card X<27) :
    ¬Nonempty (D.Simple≃*MonsterY443Derived) := by
  rintro ⟨e⟩
  exact (not_lt_of_ge (degree_ge_twentySeven D e)) hn

end SymmetricSubgroupAsymptotics.CFSGAxiomMonsterY443SmallAction
