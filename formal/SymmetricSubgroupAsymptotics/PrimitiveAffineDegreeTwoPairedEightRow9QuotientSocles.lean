import SymmetricSubgroupAsymptotics.NormalChainSocleGenerators
import SymmetricSubgroupAsymptotics.SocleNormalGeneratorNumber
import Mathlib.Order.Fin.Basic
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameTop9NormalCertificate

/-!
# Quotient socles for paired-eight row nine

The five normal states form a chain, using four existing normal-join word
certificates. The chain theorem handles every quotient without new group
membership tables.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoPairedEightRow9QuotientSocles

abbrev Source := PrimitiveAffineEightFrameTop9TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameTop9TopCertificate.group

abbrev Top := Subgroup.closure
  (Set.range PrimitiveAffineEightFrameTop9TopCertificate.generators)

private def state (i : Fin 5) : Subgroup Source :=
  Subgroup.closure (Set.range (PrimitiveAffineEightFrameTop9NormalCertificate.stateGenerators i))

private theorem state_total (i j : Fin 5) : state i ≤ state j ∨ state j ≤ state i := by
  have h01 : state 0 ≤ state 1 :=
    (PrimitiveAffineEightFrameTop9NormalCertificate.transition 0 3).parentToChild.closure_le
  have h12 : state 1 ≤ state 2 :=
    (PrimitiveAffineEightFrameTop9NormalCertificate.transition 1 2).parentToChild.closure_le
  have h23 : state 2 ≤ state 3 :=
    (PrimitiveAffineEightFrameTop9NormalCertificate.transition 2 1).parentToChild.closure_le
  have h34 : state 3 ≤ state 4 :=
    (PrimitiveAffineEightFrameTop9NormalCertificate.transition 3 4).parentToChild.closure_le
  have hmono : Monotone state := Fin.monotone_iff_le_succ.mpr (by
    intro k
    fin_cases k
    · exact h01
    · exact h12
    · exact h23
    · exact h34)
  exact (le_total i j).elim (fun h ↦ Or.inl (hmono h)) (fun h ↦ Or.inr (hmono h))

theorem source_normal_total (N M : Subgroup Source) (hN : N.Normal) (hM : M.Normal) :
    N ≤ M ∨ M ≤ N := by
  letI := hN
  letI := hM
  obtain ⟨i, rfl⟩ := PrimitiveAffineEightFrameTop9NormalCertificate.complete N
  obtain ⟨j, rfl⟩ := PrimitiveAffineEightFrameTop9NormalCertificate.complete M
  exact state_total i j

theorem top_normal_total (N M : Subgroup Top) (hN : N.Normal) (hM : M.Normal) :
    N ≤ M ∨ M ≤ N :=
  normalSubgroups_total_of_surjective
    PrimitiveAffineEightFrameTop9TopCertificate.originalEquiv.toMonoidHom
    PrimitiveAffineEightFrameTop9TopCertificate.originalEquiv.surjective
    source_normal_total N M hN hM

theorem quotientSocle_one (N : Subgroup Top) [N.Normal] :
    SocleNormalGeneratorBound (Top ⧸ N) 1 :=
  quotientSocleNormalGeneratorBound_one_of_normal_total top_normal_total N

theorem topSocle (N : {N : Subgroup Top // N.Normal}) :
    SocleNormalGeneratorBound (Top ⧸ N.1) 2 := by
  letI := N.2
  exact SocleNormalGeneratorBound.mono (quotientSocle_one N.1) (by decide)

end PrimitiveAffineDegreeTwoPairedEightRow9QuotientSocles
end SymmetricSubgroupAsymptotics

end
