import SymmetricSubgroupAsymptotics.BinaryDegreeEightPhysicalAnalyticClosure
import SymmetricSubgroupAsymptotics.BinaryOriginalWeightedDirectEntry
import SymmetricSubgroupAsymptotics.BinarySmallWidthCharacterConversion

/-!
# Parity-retaining direct coverage in degree eight

The original degree-eight finite-entry predicate retained an actual physical
pair certificate but forgot that the selected cover degree is even.  That
loss is harmless for the finite structural split, but it prevents the pair
from entering the even-prefix direct recurrence.

This file reuses the same generated registries without changing them.  It
checks parity on the canonical installed arrays before existentially hiding
the selected certificate, converts the ten character rows to the installed
seven-character direct entry, and retains the three exceptional carrier
charts.  The final theorem is on the literal original action and normal; the
single ambient conjugation used by the degree-eight action registry is pulled
back only after the weighted entry has been constructed.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics.BinaryDegreeEightDirectEntryCoverage

open SymmetricSubgroupAsymptotics
open BinaryActionRegistry8
open BinaryNormalCoverage8
open BinaryDegreeEightPhysicalAnalyticClosure

/-- The common direct interface specialized to eight physical points. -/
abbrev DirectEntry8 (U : Subgroup (Equiv.Perm (Fin 8)))
    (N : Subgroup U) [N.Normal] :=
  @BinaryOriginalWeightedDirectEntry 4 U N inferInstance

/-- The exact local output of the nonbase degree-eight registry. -/
def WeightedFiniteEntry8 (U : Subgroup (Equiv.Perm (Fin 8)))
    (N : Subgroup U) [N.Normal] : Prop :=
  Nonempty (DirectEntry8 U N) ∨
    ∃ e : Fin 3, (binaryEightTransportChart e).source = U ∧
      (binaryEightTransportChart e).axis = N.map U.subtype

/-- Install one generated local pair certificate directly into the common
weighted interface, retaining its proved even cover degree. -/
def ofInstalledPair {U : Subgroup (Equiv.Perm (Fin 8))}
    (hU : IsPGroup 2 U) {k r : ℕ} (F : BinaryPairFrame U (Fin k))
    (generators : Fin r → U)
    (generators_full : Subgroup.closure (Set.range generators) = ⊤)
    {N : Subgroup U} [N.Normal]
    (C : BinaryPairLocalCertificate generators F.top N)
    (hwidth : C.width = Nat.card (Fin 8))
    (heven : Even C.coverDegree) : DirectEntry8 U N :=
  BinaryOriginalWeightedDirectEntry.ofPair (h := 4) hU
    (BinaryPhysicalPairCertificate.ofLocal F generators generators_full C hwidth) heven

/-- At width eight, every old checked character row satisfies the installed
seven-character criterion and hence is an unconditional direct entry. -/
def ofCharacter {U : Subgroup (Equiv.Perm (Fin 8))}
    (hU : IsPGroup 2 U) {N : Subgroup U} [N.Normal]
    (C : BinaryNormalCharacterCriterion (U ⧸ N) 8) : DirectEntry8 U N :=
  BinaryOriginalWeightedDirectEntry.ofOrderSevenCharacter (h := 4)
    (by decide) hU
    (.inr (C.toSevenOfSmallWidth (Or.inr (Or.inl rfl))))

/-! ## The eighteen nonbase action representatives -/

namespace T1
open BinaryPairInstalled8T1

theorem physical_cover_even (j : Fin 4) :
    Even (physicalCertificates j).coverDegree := by
  fin_cases j <;> decide +kernel

theorem weightedEntryCoverage (N : Subgroup Original) [N.Normal] :
    WeightedFiniteEntry8 Original N := by
  rcases normal_coverage N with ⟨j,rfl⟩ | ⟨i,hi,_he⟩
  · exact Or.inl ⟨ofInstalledPair original_isPGroup frame generators generators_full
      (physicalCertificates j) (physical_width j) (physical_cover_even j)⟩
  · exfalso
    simpa [residualIndices] using hi

end T1

namespace T2
open BinaryPairInstalled8T2

theorem physical_cover_even (j : Fin 8) :
    Even (physicalCertificates j).coverDegree := by
  fin_cases j <;> decide +kernel

theorem weightedEntryCoverage (N : Subgroup Original) [N.Normal] :
    WeightedFiniteEntry8 Original N := by
  rcases normal_coverage N with ⟨j,rfl⟩ | ⟨i,hi,_he⟩
  · exact Or.inl ⟨ofInstalledPair original_isPGroup frame generators generators_full
      (physicalCertificates j) (physical_width j) (physical_cover_even j)⟩
  · exfalso
    simpa [residualIndices] using hi

end T2

namespace T3
open BinaryPairInstalled8T3

theorem physical_cover_even (j : Fin 16) :
    Even (physicalCertificates j).coverDegree := by
  fin_cases j <;> decide +kernel

theorem weightedEntryCoverage (N : Subgroup Original) [N.Normal] :
    WeightedFiniteEntry8 Original N := by
  rcases normal_coverage N with ⟨j,rfl⟩ | ⟨i,hi,_he⟩
  · exact Or.inl ⟨ofInstalledPair original_isPGroup frame generators generators_full
      (physicalCertificates j) (physical_width j) (physical_cover_even j)⟩
  · exfalso
    simpa [residualIndices] using hi

end T3

namespace T4
open BinaryPairInstalled8T4

theorem physical_cover_even (j : Fin 6) :
    Even (physicalCertificates j).coverDegree := by
  fin_cases j <;> decide +kernel

theorem weightedEntryCoverage (N : Subgroup Original) [N.Normal] :
    WeightedFiniteEntry8 Original N := by
  rcases normal_coverage N with ⟨j,rfl⟩ | ⟨i,hi,_he⟩
  · exact Or.inl ⟨ofInstalledPair original_isPGroup frame generators generators_full
      (physicalCertificates j) (physical_width j) (physical_cover_even j)⟩
  · exfalso
    simpa [residualIndices] using hi

end T4

namespace T5
open BinaryPairInstalled8T5

theorem physical_cover_even (j : Fin 6) :
    Even (physicalCertificates j).coverDegree := by
  fin_cases j <;> decide +kernel

theorem weightedEntryCoverage (N : Subgroup Original) [N.Normal] :
    WeightedFiniteEntry8 Original N := by
  rcases normal_coverage N with ⟨j,rfl⟩ | ⟨i,hi,_he⟩
  · exact Or.inl ⟨ofInstalledPair original_isPGroup frame generators generators_full
      (physicalCertificates j) (physical_width j) (physical_cover_even j)⟩
  · exfalso
    simpa [residualIndices] using hi

end T5

namespace T6
open BinaryPairInstalled8T6

theorem physical_cover_even (j : Fin 7) :
    Even (physicalCertificates j).coverDegree := by
  fin_cases j <;> decide +kernel

theorem weightedEntryCoverage (N : Subgroup Original) [N.Normal] :
    WeightedFiniteEntry8 Original N := by
  rcases normal_coverage N with ⟨j,rfl⟩ | ⟨i,hi,_he⟩
  · exact Or.inl ⟨ofInstalledPair original_isPGroup frame generators generators_full
      (physicalCertificates j) (physical_width j) (physical_cover_even j)⟩
  · exfalso
    simpa [residualIndices] using hi

end T6

namespace T7
open BinaryPairInstalled8T7

theorem physical_cover_even (j : Fin 8) :
    Even (physicalCertificates j).coverDegree := by
  fin_cases j <;> decide +kernel

theorem weightedEntryCoverage (N : Subgroup Original) [N.Normal] :
    WeightedFiniteEntry8 Original N := by
  rcases normal_coverage N with ⟨j,rfl⟩ | ⟨i,hi,he⟩
  · exact Or.inl ⟨ofInstalledPair original_isPGroup frame generators generators_full
      (physicalCertificates j) (physical_width j) (physical_cover_even j)⟩
  · have hi0 : i = 0 := by simpa [residualIndices] using hi
    subst i
    cases he
    exact Or.inl ⟨ofCharacter original_isPGroup
      BinaryNormalCharacters8T7.N0.physicalCriterion⟩

end T7

namespace T8
open BinaryPairInstalled8T8

theorem physical_cover_even (j : Fin 7) :
    Even (physicalCertificates j).coverDegree := by
  fin_cases j <;> decide +kernel

theorem weightedEntryCoverage (N : Subgroup Original) [N.Normal] :
    WeightedFiniteEntry8 Original N := by
  rcases normal_coverage N with ⟨j,rfl⟩ | ⟨i,hi,_he⟩
  · exact Or.inl ⟨ofInstalledPair original_isPGroup frame generators generators_full
      (physicalCertificates j) (physical_width j) (physical_cover_even j)⟩
  · exfalso
    simpa [residualIndices] using hi

end T8

namespace T9
open BinaryPairInstalled8T9

theorem physical_cover_even (j : Fin 19) :
    Even (physicalCertificates j).coverDegree := by
  fin_cases j <;> decide +kernel

theorem weightedEntryCoverage (N : Subgroup Original) [N.Normal] :
    WeightedFiniteEntry8 Original N := by
  rcases normal_coverage N with ⟨j,rfl⟩ | ⟨i,hi,_he⟩
  · exact Or.inl ⟨ofInstalledPair original_isPGroup frame generators generators_full
      (physicalCertificates j) (physical_width j) (physical_cover_even j)⟩
  · exfalso
    simpa [residualIndices] using hi

end T9

namespace T10
open BinaryPairInstalled8T10

theorem physical_cover_even (j : Fin 11) :
    Even (physicalCertificates j).coverDegree := by
  fin_cases j <;> decide +kernel

theorem weightedEntryCoverage (N : Subgroup Original) [N.Normal] :
    WeightedFiniteEntry8 Original N := by
  rcases normal_coverage N with ⟨j,rfl⟩ | ⟨i,hi,_he⟩
  · exact Or.inl ⟨ofInstalledPair original_isPGroup frame generators generators_full
      (physicalCertificates j) (physical_width j) (physical_cover_even j)⟩
  · exfalso
    simpa [residualIndices] using hi

end T10

namespace T11
open BinaryPairInstalled8T11

theorem physical_cover_even (j : Fin 16) :
    Even (physicalCertificates j).coverDegree := by
  fin_cases j <;> decide +kernel

theorem weightedEntryCoverage (N : Subgroup Original) [N.Normal] :
    WeightedFiniteEntry8 Original N := by
  rcases normal_coverage N with ⟨j,rfl⟩ | ⟨i,hi,he⟩
  · exact Or.inl ⟨ofInstalledPair original_isPGroup frame generators generators_full
      (physicalCertificates j) (physical_width j) (physical_cover_even j)⟩
  · have hi0 : i = 0 := by simpa [residualIndices] using hi
    subst i
    cases he
    exact Or.inl ⟨ofCharacter original_isPGroup
      BinaryNormalCharacters8T11.N0.physicalCriterion⟩

end T11

namespace T15
open BinaryPairInstalled8T15

theorem physical_cover_even (j : Fin 19) :
    Even (physicalCertificates j).coverDegree := by
  fin_cases j <;> decide +kernel

theorem weightedEntryCoverage (N : Subgroup Original) [N.Normal] :
    WeightedFiniteEntry8 Original N := by
  rcases normal_coverage N with ⟨j,rfl⟩ | ⟨i,hi,he⟩
  · exact Or.inl ⟨ofInstalledPair original_isPGroup frame generators generators_full
      (physicalCertificates j) (physical_width j) (physical_cover_even j)⟩
  · have hi0 : i = 0 := by simpa [residualIndices] using hi
    subst i
    cases he
    exact Or.inl ⟨ofCharacter original_isPGroup
      BinaryNormalCharacters8T15.N0.physicalCriterion⟩

end T15

namespace T16
open BinaryPairInstalled8T16

theorem physical_cover_even (j : Fin 10) :
    Even (physicalCertificates j).coverDegree := by
  fin_cases j <;> decide +kernel

theorem weightedEntryCoverage (N : Subgroup Original) [N.Normal] :
    WeightedFiniteEntry8 Original N := by
  rcases normal_coverage N with ⟨j,rfl⟩ | ⟨i,hi,he⟩
  · exact Or.inl ⟨ofInstalledPair original_isPGroup frame generators generators_full
      (physicalCertificates j) (physical_width j) (physical_cover_even j)⟩
  · have hi01 : i = 0 ∨ i = 1 := by simpa [residualIndices] using hi
    rcases hi01 with rfl | rfl
    · cases he
      exact Or.inl ⟨ofCharacter original_isPGroup
        BinaryNormalCharacters8T16.N0.physicalCriterion⟩
    · cases he
      exact Or.inr ⟨0,BinaryNormalTransport8T16.source_eq,
        BinaryNormalTransport8T16.axis_eq⟩

end T16

namespace T17
open BinaryPairInstalled8T17

theorem physical_cover_even (j : Fin 11) :
    Even (physicalCertificates j).coverDegree := by
  fin_cases j <;> decide +kernel

theorem weightedEntryCoverage (N : Subgroup Original) [N.Normal] :
    WeightedFiniteEntry8 Original N := by
  rcases normal_coverage N with ⟨j,rfl⟩ | ⟨i,hi,he⟩
  · exact Or.inl ⟨ofInstalledPair original_isPGroup frame generators generators_full
      (physicalCertificates j) (physical_width j) (physical_cover_even j)⟩
  · have hi0 : i = 0 := by simpa [residualIndices] using hi
    subst i
    cases he
    exact Or.inl ⟨ofCharacter original_isPGroup
      BinaryNormalCharacters8T17.N0.physicalCriterion⟩

end T17

namespace T19
open BinaryPairInstalled8T19

theorem physical_cover_even (j : Fin 11) :
    Even (physicalCertificates j).coverDegree := by
  fin_cases j <;> decide +kernel

theorem weightedEntryCoverage (N : Subgroup Original) [N.Normal] :
    WeightedFiniteEntry8 Original N := by
  rcases normal_coverage N with ⟨j,rfl⟩ | ⟨i,hi,he⟩
  · exact Or.inl ⟨ofInstalledPair original_isPGroup frame generators generators_full
      (physicalCertificates j) (physical_width j) (physical_cover_even j)⟩
  · have hi0 : i = 0 := by simpa [residualIndices] using hi
    subst i
    cases he
    exact Or.inl ⟨ofCharacter original_isPGroup
      BinaryNormalCharacters8T19.N0.physicalCriterion⟩

end T19

namespace T20
open BinaryPairInstalled8T20

theorem physical_cover_even (j : Fin 10) :
    Even (physicalCertificates j).coverDegree := by
  fin_cases j <;> decide +kernel

theorem weightedEntryCoverage (N : Subgroup Original) [N.Normal] :
    WeightedFiniteEntry8 Original N := by
  rcases normal_coverage N with ⟨j,rfl⟩ | ⟨i,hi,he⟩
  · exact Or.inl ⟨ofInstalledPair original_isPGroup frame generators generators_full
      (physicalCertificates j) (physical_width j) (physical_cover_even j)⟩
  · have hi01 : i = 0 ∨ i = 1 := by simpa [residualIndices] using hi
    rcases hi01 with rfl | rfl
    · cases he
      exact Or.inl ⟨ofCharacter original_isPGroup
        BinaryNormalCharacters8T20.N0.physicalCriterion⟩
    · cases he
      exact Or.inr ⟨1,BinaryNormalTransport8T20.source_eq,
        BinaryNormalTransport8T20.axis_eq⟩

end T20

namespace T21
open BinaryPairInstalled8T21

theorem physical_cover_even (j : Fin 10) :
    Even (physicalCertificates j).coverDegree := by
  fin_cases j <;> decide +kernel

theorem weightedEntryCoverage (N : Subgroup Original) [N.Normal] :
    WeightedFiniteEntry8 Original N := by
  rcases normal_coverage N with ⟨j,rfl⟩ | ⟨i,hi,he⟩
  · exact Or.inl ⟨ofInstalledPair original_isPGroup frame generators generators_full
      (physicalCertificates j) (physical_width j) (physical_cover_even j)⟩
  · have hi01 : i = 0 ∨ i = 1 := by simpa [residualIndices] using hi
    rcases hi01 with rfl | rfl
    · cases he
      exact Or.inl ⟨ofCharacter original_isPGroup
        BinaryNormalCharacters8T21.N0.physicalCriterion⟩
    · cases he
      exact Or.inr ⟨2,BinaryNormalTransport8T21.source_eq,
        BinaryNormalTransport8T21.axis_eq⟩

end T21

namespace T30
open BinaryPairInstalled8T30

theorem physical_cover_even (j : Fin 11) :
    Even (physicalCertificates j).coverDegree := by
  fin_cases j <;> decide +kernel

theorem weightedEntryCoverage (N : Subgroup Original) [N.Normal] :
    WeightedFiniteEntry8 Original N := by
  rcases normal_coverage N with ⟨j,rfl⟩ | ⟨i,hi,he⟩
  · exact Or.inl ⟨ofInstalledPair original_isPGroup frame generators generators_full
      (physicalCertificates j) (physical_width j) (physical_cover_even j)⟩
  · have hi01 : i = 0 ∨ i = 1 := by simpa [residualIndices] using hi
    rcases hi01 with rfl | rfl
    · cases he
      exact Or.inl ⟨ofCharacter original_isPGroup
        BinaryNormalCharacters8T30.N0.physicalCriterion⟩
    · cases he
      exact Or.inl ⟨ofCharacter original_isPGroup
        BinaryNormalCharacters8T30.N1.physicalCriterion⟩

end T30

/-! ## Aggregation and return to the literal original action -/

/-- Every nonbase registry action has either an unconditional weighted direct
entry on the exact normal or one of the three checked carrier charts. -/
theorem finiteWeightedEntryCoverage (i : Fin 26) (hi : i ∉ baseIndices)
    (N : Subgroup (actions i)) [hN : N.Normal] :
    WeightedFiniteEntry8 (actions i) N := by
  fin_cases i
  · exact @T1.weightedEntryCoverage N hN
  · exact @T2.weightedEntryCoverage N hN
  · exact @T3.weightedEntryCoverage N hN
  · exact @T4.weightedEntryCoverage N hN
  · exact @T5.weightedEntryCoverage N hN
  · exact @T6.weightedEntryCoverage N hN
  · exact @T7.weightedEntryCoverage N hN
  · exact @T8.weightedEntryCoverage N hN
  · exact @T9.weightedEntryCoverage N hN
  · exact @T10.weightedEntryCoverage N hN
  · exact @T11.weightedEntryCoverage N hN
  · exact @T15.weightedEntryCoverage N hN
  · exact @T16.weightedEntryCoverage N hN
  · exact @T17.weightedEntryCoverage N hN
  · exact False.elim (hi (by decide +kernel))
  · exact @T19.weightedEntryCoverage N hN
  · exact @T20.weightedEntryCoverage N hN
  · exact @T21.weightedEntryCoverage N hN
  · exact False.elim (hi (by decide +kernel))
  · exact False.elim (hi (by decide +kernel))
  · exact False.elim (hi (by decide +kernel))
  · exact False.elim (hi (by decide +kernel))
  · exact False.elim (hi (by decide +kernel))
  · exact @T30.weightedEntryCoverage N hN
  · exact False.elim (hi (by decide +kernel))
  · exact False.elim (hi (by decide +kernel))

/-- Pull a weighted entry through the one point conjugation supplied by the
action registry.  The generic entry transport retains the numerical
parameters and all same-source moments. -/
def pullbackConjugateEntry
    {U V : Subgroup (Equiv.Perm (Fin 8))}
    {N : Subgroup U} [N.Normal]
    (g : Equiv.Perm (Fin 8)) (hg : MulAut.conj g • U = V)
    (E : DirectEntry8 V (actionConjugacyNormal g hg N)) :
    DirectEntry8 U N := by
  have haxis :
      (actionConjugacyNormal g hg N).map
        (actionConjugacyEquiv g hg).symm.toMonoidHom = N := by
    rw [actionConjugacyNormal,Subgroup.map_map]
    simpa using Subgroup.map_id N
  exact BinaryOriginalWeightedDirectEntry.transport
    (actionConjugacyEquiv g hg).symm haxis E

/-- Full local degree-eight closure with the direct branch already converted
to the common weighted recurrence interface on the literal original action. -/
theorem complete_axis_weighted_or_carrier
    (U : Subgroup (Equiv.Perm (Fin 8))) (hU : IsPGroup 2 U)
    (ht : PermutationSubgroupTransitive U)
    (N : Subgroup U) [N.Normal] :
    Nonempty (DirectEntry8 U N) ∨ CarrierOwner U N := by
  obtain ⟨i,g,hg⟩ := BinaryActionRegistry8.complete U hU ht
  by_cases hi : i ∈ baseIndices
  · obtain ⟨b,hb⟩ := (mem_baseIndices_iff i).mp hi
    subst i
    exact Or.inr (.base b g hg)
  · rcases finiteWeightedEntryCoverage i hi
      (actionConjugacyNormal g hg N) with hentry | hcarrier
    · obtain ⟨E⟩ := hentry
      exact Or.inl ⟨pullbackConjugateEntry g hg E⟩
    · obtain ⟨e,hsource,haxis⟩ := hcarrier
      exact Or.inr (.exceptional i g hg e hsource haxis)

end SymmetricSubgroupAsymptotics.BinaryDegreeEightDirectEntryCoverage

end
