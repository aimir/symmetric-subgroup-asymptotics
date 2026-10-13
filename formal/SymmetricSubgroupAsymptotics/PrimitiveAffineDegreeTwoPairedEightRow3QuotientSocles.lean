import SymmetricSubgroupAsymptotics.NormalChainCoverSocleGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow2NormalCertificate
import Mathlib.Order.Fin.Basic

/-!
# All quotient socles for paired-eight row three

The existing seven-state normal registry is covered by two chains. Its
normal-join inclusions certify these chains, and the shared chain-cover
theorem gives a two-generator socle for every quotient of the literal top.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoPairedEightRow3QuotientSocles

abbrev Source := PrimitiveAffineEightFrameRow2TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameRow2TopCertificate.group

abbrev Top := Subgroup.closure
  (Set.range PrimitiveAffineEightFrameRow2TopCertificate.generators)

private def state (i : Fin 7) : Subgroup Source :=
  Subgroup.closure (Set.range (PrimitiveAffineEightFrameRow2NormalCertificate.stateGenerators i))

private def chainIndex : Fin 2 → Fin 5 → Fin 7 :=
  ![![0, 1, 2, 4, 6], ![0, 1, 3, 5, 6]]

private theorem chains_monotone (i : Fin 2) :
    Monotone (fun j ↦ state (chainIndex i j)) := by
  have h01 : state 0 ≤ state 1 :=
    (PrimitiveAffineEightFrameRow2NormalCertificate.transition 0 6).parentToChild.closure_le
  have h12 : state 1 ≤ state 2 :=
    (PrimitiveAffineEightFrameRow2NormalCertificate.transition 1 3).parentToChild.closure_le
  have h24 : state 2 ≤ state 4 :=
    (PrimitiveAffineEightFrameRow2NormalCertificate.transition 2 2).parentToChild.closure_le
  have h46 : state 4 ≤ state 6 :=
    (PrimitiveAffineEightFrameRow2NormalCertificate.transition 4 1).parentToChild.closure_le
  have h13 : state 1 ≤ state 3 :=
    (PrimitiveAffineEightFrameRow2NormalCertificate.transition 1 2).parentToChild.closure_le
  have h35 : state 3 ≤ state 5 :=
    (PrimitiveAffineEightFrameRow2NormalCertificate.transition 3 1).parentToChild.closure_le
  have h56 : state 5 ≤ state 6 :=
    (PrimitiveAffineEightFrameRow2NormalCertificate.transition 5 3).parentToChild.closure_le
  apply Fin.monotone_iff_le_succ.mpr
  intro j
  fin_cases i <;> fin_cases j
  · exact h01
  · exact h12
  · exact h24
  · exact h46
  · exact h01
  · exact h13
  · exact h35
  · exact h56

/-- The two chains cover the complete literal normal registry. -/
noncomputable def sourceChainCover : NormalSubgroupChainCover Source 2 :=
  NormalSubgroupChainCover.ofFiniteChains (fun i j ↦ state (chainIndex i j))
    chains_monotone (by
      intro N hN
      letI := hN
      obtain ⟨s, rfl⟩ := PrimitiveAffineEightFrameRow2NormalCertificate.complete N
      have h : ∀ s : Fin 7, ∃ i j, chainIndex i j = s := by decide +kernel
      obtain ⟨i, j, h⟩ := h s
      exact ⟨i, j, congrArg state h⟩)

/-- Transport the chains through the checked equivalence with the literal action. -/
noncomputable def topChainCover : NormalSubgroupChainCover Top 2 :=
  sourceChainCover.ofSurjective
    PrimitiveAffineEightFrameRow2TopCertificate.originalEquiv.toMonoidHom
    PrimitiveAffineEightFrameRow2TopCertificate.originalEquiv.surjective

theorem topSocle (N : {N : Subgroup Top // N.Normal}) :
    SocleNormalGeneratorBound (Top ⧸ N.1) 2 := by
  letI := N.2
  exact topChainCover.quotientSocleBound N.1

end PrimitiveAffineDegreeTwoPairedEightRow3QuotientSocles
end SymmetricSubgroupAsymptotics

end
