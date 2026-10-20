import SymmetricSubgroupAsymptotics.NormalChainSocleGenerators
import SymmetricSubgroupAsymptotics.SocleNormalGeneratorNumber
import Mathlib.Order.Fin.Basic
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow29NormalCertificate

/-!
# Quotient socles for paired-eight row twenty-two

The three normal states form a chain, using two existing normal-join word
certificates. The chain theorem handles every quotient without new group
membership tables.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoPairedEightRow22QuotientSocles

abbrev Source := PrimitiveAffineEightFrameRow29TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameRow29TopCertificate.group

abbrev Top := Subgroup.closure
  (Set.range PrimitiveAffineEightFrameRow29TopCertificate.generators)

private def state (i : Fin 3) : Subgroup Source :=
  Subgroup.closure (Set.range (PrimitiveAffineEightFrameRow29NormalCertificate.stateGenerators i))

private theorem state_total (i j : Fin 3) : state i ≤ state j ∨ state j ≤ state i := by
  have h01 : state 0 ≤ state 1 :=
    (PrimitiveAffineEightFrameRow29NormalCertificate.transition 0 1).parentToChild.closure_le
  have h12 : state 1 ≤ state 2 :=
    (PrimitiveAffineEightFrameRow29NormalCertificate.transition 1 2).parentToChild.closure_le
  have hmono : Monotone state := Fin.monotone_iff_le_succ.mpr (by
    intro k
    fin_cases k
    · exact h01
    · exact h12)
  exact (le_total i j).elim (fun h ↦ Or.inl (hmono h)) (fun h ↦ Or.inr (hmono h))

theorem source_normal_total (N M : Subgroup Source) (hN : N.Normal) (hM : M.Normal) :
    N ≤ M ∨ M ≤ N := by
  letI := hN
  letI := hM
  obtain ⟨i, rfl⟩ := PrimitiveAffineEightFrameRow29NormalCertificate.complete N
  obtain ⟨j, rfl⟩ := PrimitiveAffineEightFrameRow29NormalCertificate.complete M
  exact state_total i j

theorem top_normal_total (N M : Subgroup Top) (hN : N.Normal) (hM : M.Normal) :
    N ≤ M ∨ M ≤ N :=
  normalSubgroups_total_of_surjective
    PrimitiveAffineEightFrameRow29TopCertificate.originalEquiv.toMonoidHom
    PrimitiveAffineEightFrameRow29TopCertificate.originalEquiv.surjective
    source_normal_total N M hN hM

theorem quotientSocle_one (N : Subgroup Top) [N.Normal] :
    SocleNormalGeneratorBound (Top ⧸ N) 1 :=
  quotientSocleNormalGeneratorBound_one_of_normal_total top_normal_total N

theorem topSocle (N : {N : Subgroup Top // N.Normal}) :
    SocleNormalGeneratorBound (Top ⧸ N.1) 2 := by
  letI := N.2
  exact SocleNormalGeneratorBound.mono (quotientSocle_one N.1) (by decide)

end PrimitiveAffineDegreeTwoPairedEightRow22QuotientSocles
end SymmetricSubgroupAsymptotics

end
