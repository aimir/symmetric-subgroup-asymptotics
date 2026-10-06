import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow28NormalCertificate
import SymmetricSubgroupAsymptotics.FiniteTopRelativeBinaryRankWordRegistry
import SymmetricSubgroupAsymptotics.NormalOrderTwo

/-!
# Selected row 28: relative binary heads of the order-168 top

The checked normal-join registry has exactly two states.  The bottom state
has zero relative head.  For the nontrivial state, its first generator has a
nontrivial square.  Since every square belongs to the relative binary
radical, completeness of the two-state normal registry forces that radical
to be the full state.  Thus its relative head is also zero.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow28TopRegistry

abbrev Source := PrimitiveAffineEightFrameRow28NormalCertificate.Source
local instance sourceGroup : Group Source :=
  PrimitiveAffineEightFrameRow28TopCertificate.group

private abbrev N0 : Subgroup Source :=
  Subgroup.closure (Set.range (PrimitiveAffineEightFrameRow28NormalCertificate.stateGenerators 0))

private abbrev N1 : Subgroup Source :=
  Subgroup.closure (Set.range (PrimitiveAffineEightFrameRow28NormalCertificate.stateGenerators 1))

local instance n0Normal : N0.Normal :=
  (PrimitiveAffineEightFrameRow28NormalCertificate.data.normality 0).normal PrimitiveAffineEightFrameRow28NormalCertificate.data.ambient_full

local instance n1Normal : N1.Normal :=
  (PrimitiveAffineEightFrameRow28NormalCertificate.data.normality 1).normal PrimitiveAffineEightFrameRow28NormalCertificate.data.ambient_full

private theorem n0_eq_bot : N0 = ⊥ := by
  simpa only [PrimitiveAffineEightFrameRow28NormalCertificate.data] using
    PrimitiveAffineEightFrameRow28NormalCertificate.data.bottom_eq

private theorem radical_zero_eq : primeRelativeRadical 2 N0 = N0 := by
  apply le_antisymm (primeRelativeRadical_le 2 N0)
  exact n0_eq_bot.le.trans bot_le

private theorem radical_one_eq : primeRelativeRadical 2 N1 = N1 := by
  let R : Subgroup Source := primeRelativeRadical 2 N1
  letI : R.Normal := inferInstance
  obtain ⟨i, hi⟩ := PrimitiveAffineEightFrameRow28NormalCertificate.complete R
  fin_cases i
  · have hR : R = ⊥ := hi.symm.trans PrimitiveAffineEightFrameRow28NormalCertificate.data.bottom_eq
    have hpow : (PrimitiveAffineEightFrameRow28NormalCertificate.stateGenerators 1 0) ^ 2 ∈ R :=
      pow_mem_primeRelativeRadical 2 N1
        ⟨PrimitiveAffineEightFrameRow28NormalCertificate.stateGenerators 1 0,
          Subgroup.subset_closure (Set.mem_range_self 0)⟩
    rw [hR, Subgroup.mem_bot] at hpow
    have hne : (PrimitiveAffineEightFrameRow28NormalCertificate.stateGenerators 1 0) ^ 2 ≠ (1 : Source) := by
      native_decide
    exact (hne hpow).elim
  · exact hi.symm

private theorem head_zero (i : Fin 2) :
    letI : (Subgroup.closure
        (Set.range (PrimitiveAffineEightFrameRow28NormalCertificate.stateGenerators i))).Normal :=
      (PrimitiveAffineEightFrameRow28NormalCertificate.data.normality i).normal PrimitiveAffineEightFrameRow28NormalCertificate.data.ambient_full
    Module.finrank (ZMod 2)
      (primeRelativeCharacters 2
        (Subgroup.closure (Set.range (PrimitiveAffineEightFrameRow28NormalCertificate.stateGenerators i)))) = 0 := by
  fin_cases i
  · exact primeRelativeHead_eq_of_radical_card 2 N0 N0 0
      radical_zero_eq (by simp)
  · exact primeRelativeHead_eq_of_radical_card 2 N1 N1 0
      radical_one_eq (by simp)

/-- The literal order-168 top has relative binary head zero at every normal
axis; the five-slot consumer only asks for the weaker bound by two. -/
noncomputable def registry : FiniteTopRelativeBinaryRankWordRegistry
    (rank := 2) PrimitiveAffineEightFrameRow28NormalCertificate.topConjugacy.toCardinalCover PrimitiveAffineEightFrameRow28NormalCertificate.topAmbient
      PrimitiveAffineEightFrameRow28NormalCertificate.stateGenerators where
  indexFinite := inferInstance
  data := PrimitiveAffineEightFrameRow28NormalCertificate.data
  head_le i := by
    rw [head_zero i]
    omega

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow28TopRegistry

end
