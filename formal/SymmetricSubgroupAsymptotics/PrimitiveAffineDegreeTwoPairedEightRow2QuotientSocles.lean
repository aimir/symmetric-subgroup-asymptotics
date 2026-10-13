import SymmetricSubgroupAsymptotics.NormalChainSocleGenerators
import Mathlib.Order.Fin.Basic
import SymmetricSubgroupAsymptotics.SocleNormalGeneratorNumber
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1NormalCertificate

/-!
# Quotient socles for paired-eight row two

Three inclusions from the existing normal-join word registry establish a
chain containing every normal subgroup. The general normal-chain theorem
then handles all quotient socles at once. No second group table or separate
normal-generating tuple for each quotient is needed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoPairedEightRow2QuotientSocles

abbrev Source := PrimitiveAffineEightFrameRow1TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameRow1TopCertificate.group

abbrev Top := Subgroup.closure
  (Set.range PrimitiveAffineEightFrameRow1TopCertificate.generators)

private def state (i : Fin 4) : Subgroup Source :=
  Subgroup.closure (Set.range (PrimitiveAffineEightFrameRow1NormalCertificate.stateGenerators i))

private theorem state_total (i j : Fin 4) : state i ≤ state j ∨ state j ≤ state i := by
  have h01 : state 0 ≤ state 1 :=
    (PrimitiveAffineEightFrameRow1NormalCertificate.transition 0 2).parentToChild.closure_le
  have h12 : state 1 ≤ state 2 :=
    (PrimitiveAffineEightFrameRow1NormalCertificate.transition 1 1).parentToChild.closure_le
  have h23 : state 2 ≤ state 3 :=
    (PrimitiveAffineEightFrameRow1NormalCertificate.transition 2 3).parentToChild.closure_le
  have hmono : Monotone state := Fin.monotone_iff_le_succ.mpr (by
    intro k
    fin_cases k
    · exact h01
    · exact h12
    · exact h23)
  exact (le_total i j).elim (fun h ↦ Or.inl (hmono h)) (fun h ↦ Or.inr (hmono h))

theorem source_normal_total (N M : Subgroup Source) (hN : N.Normal) (hM : M.Normal) :
    N ≤ M ∨ M ≤ N := by
  letI := hN
  letI := hM
  obtain ⟨i, rfl⟩ := PrimitiveAffineEightFrameRow1NormalCertificate.complete N
  obtain ⟨j, rfl⟩ := PrimitiveAffineEightFrameRow1NormalCertificate.complete M
  exact state_total i j

/-- Normal-chain coverage is transported to the literal eight-point action. -/
theorem top_normal_total (N M : Subgroup Top) (hN : N.Normal) (hM : M.Normal) :
    N ≤ M ∨ M ≤ N :=
  normalSubgroups_total_of_surjective
    PrimitiveAffineEightFrameRow1TopCertificate.originalEquiv.toMonoidHom
    PrimitiveAffineEightFrameRow1TopCertificate.originalEquiv.surjective
    source_normal_total N M hN hM

/-- Every normal quotient of this literal top has a one-generator socle. -/
theorem quotientSocle_one (N : Subgroup Top) [N.Normal] :
    SocleNormalGeneratorBound (Top ⧸ N) 1 :=
  quotientSocleNormalGeneratorBound_one_of_normal_total top_normal_total N

/-- Padded two-position form consumed by the shared paired-eight package. -/
theorem topSocle (N : {N : Subgroup Top // N.Normal}) :
    SocleNormalGeneratorBound (Top ⧸ N.1) 2 := by
  letI := N.2
  exact (quotientSocle_one N.1).mono (by decide)

end PrimitiveAffineDegreeTwoPairedEightRow2QuotientSocles
end SymmetricSubgroupAsymptotics

end
