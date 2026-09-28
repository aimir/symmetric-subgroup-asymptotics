import SymmetricSubgroupAsymptotics.RepeatedMarkerZeroDefect
import SymmetricSubgroupAsymptotics.TerminalContraction

/-!
# The no-selected marker-free residual is binary

The final O02 exhaustion uses only an intrinsic group-theoretic fact.  Once
every nonmarker orbit image satisfies the held binary alternative and there
are no singleton or natural-`S3` marker orbits, the complete exterior is a
`2`-group.  Its literal `O^2` residual is therefore trivial.  The proof uses
the simultaneous orbit chart, so proper subdirect products are included.

This file proves that implication on the physical exterior group.  Routing
the final O02 atoms into this state remains a separate ownership theorem.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- A binary group has trivial maximal-binary-quotient residual. -/
theorem terminalTwoResidual_eq_bot_of_isPGroup
    {T : Type*} [Group T] (hT : IsPGroup 2 T) :
    terminalTwoResidual T = ⊥ := by
  apply le_bot_iff.mp
  simpa using
    (terminalTwoResidual_le_ker (T := T) (MonoidHom.id T) hT)

/-- Exact intrinsic state left by the no-selected O02 branch: the held
orbit alphabet applies, there are no fixed or natural-`S3` markers, but the
state still claims a nontrivial `O^2` residual. -/
def NoSelectedNonbinaryResidual (X : Type) [Fintype X] :=
  {T : Subgroup (Equiv.Perm X) //
    RepeatedMarkerOrbitProfiles.Fits T ∧
      RepeatedMarkerOrbitProfiles.orbitCount T 1 +
        RepeatedMarkerOrbitProfiles.orbitCount T 3 = 0 ∧
      terminalTwoResidual T ≠ ⊥}

/-- The no-selected marker-free residual is empty.  No classification of
the ambient subgroup or of its possible proper subdirect images is used. -/
theorem noSelectedNonbinaryResidual_isEmpty
    (X : Type) [Fintype X] :
    IsEmpty (NoSelectedNonbinaryResidual X) := by
  refine ⟨?_⟩
  intro S
  have hthree : RepeatedMarkerOrbitProfiles.orbitCount S.1 3 = 0 := by
    have hsum := S.2.2.1
    omega
  have hbinary : IsPGroup 2 S.1 :=
    RepeatedMarkerZeroDefect.isPGroup_of_marker_count_zero
      S.1 S.2.1 hthree
  exact S.2.2.2 (terminalTwoResidual_eq_bot_of_isPGroup hbinary)

end SymmetricSubgroupAsymptotics

end
