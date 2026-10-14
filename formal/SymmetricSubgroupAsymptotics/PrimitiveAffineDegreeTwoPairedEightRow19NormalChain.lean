import SymmetricSubgroupAsymptotics.FiniteNormalChainGenerators
import SymmetricSubgroupAsymptotics.NormalChainSocleGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow27NormalCertificate
import Mathlib.Order.Fin.Basic

/-!
# The retained four-state normal chain for paired-eight row 19

Three existing transition certificates order all four normal states. Their
completeness therefore gives one ambient normal generator for every normal
subgroup, and a one-generator socle for every quotient of the literal top.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoPairedEightRow19NormalChain

abbrev Source := PrimitiveAffineEightFrameRow27TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameRow27TopCertificate.group

abbrev Top := Subgroup.closure
  (Set.range PrimitiveAffineEightFrameRow27TopCertificate.generators)

private def state (i : Fin 4) : Subgroup Source :=
  Subgroup.closure (Set.range (PrimitiveAffineEightFrameRow27NormalCertificate.stateGenerators i))

private theorem state_total (i j : Fin 4) : state i ≤ state j ∨ state j ≤ state i := by
  have h01 : state 0 ≤ state 1 :=
    (PrimitiveAffineEightFrameRow27NormalCertificate.transition 0 3).parentToChild.closure_le
  have h12 : state 1 ≤ state 2 :=
    (PrimitiveAffineEightFrameRow27NormalCertificate.transition 1 1).parentToChild.closure_le
  have h23 : state 2 ≤ state 3 :=
    (PrimitiveAffineEightFrameRow27NormalCertificate.transition 2 2).parentToChild.closure_le
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
  obtain ⟨i, rfl⟩ := PrimitiveAffineEightFrameRow27NormalCertificate.complete N
  obtain ⟨j, rfl⟩ := PrimitiveAffineEightFrameRow27NormalCertificate.complete M
  exact state_total i j

theorem top_normal_total (N M : Subgroup Top) (hN : N.Normal) (hM : M.Normal) :
    N ≤ M ∨ M ≤ N :=
  normalSubgroups_total_of_surjective
    PrimitiveAffineEightFrameRow27TopCertificate.originalEquiv.toMonoidHom
    PrimitiveAffineEightFrameRow27TopCertificate.originalEquiv.surjective
    source_normal_total N M hN hM

theorem top_normal_generators (N : Subgroup Top) (hN : N.Normal) :
    ∃ x : Fin 1 → Top, Subgroup.normalClosure (Set.range x) = N :=
  normal_generating_singletons_of_finite_normal_total top_normal_total N hN

theorem quotientSocle_one (N : Subgroup Top) [N.Normal] :
    SocleNormalGeneratorBound (Top ⧸ N) 1 :=
  quotientSocleNormalGeneratorBound_one_of_normal_total top_normal_total N

end PrimitiveAffineDegreeTwoPairedEightRow19NormalChain
end SymmetricSubgroupAsymptotics

end
