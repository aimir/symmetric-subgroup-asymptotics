import SymmetricSubgroupAsymptotics.TraceySharpHalfDegreeNumerics
import SymmetricSubgroupAsymptotics.McIverNeumannFromTraceyBounded
import SymmetricSubgroupAsymptotics.PermutationSmallDegreeOrdinaryGenerators

/-!
# An optional bundle of two conclusions from the same published theorem

G. Tracey, *Minimal generation of transitive permutation groups*,
Journal of Algebra 509 (2018), 40--100, Theorem 1.1(1),(2):
https://pure-oai.bham.ac.uk/ws/files/147250737/transgens1.pdf

The existing `TraceyPermutationGeneratorInput` retains a weakening of
part (1). This NEW bundle additionally retains part (2), ONLY at degrees
4 <= n < 22. Part (2)'s possible exceptional degrees are 5*2^k with
17 <= k <= 26, or 15*2^k with 15 <= k <= 35. None lies in this bounded
range, regardless of the soluble-transitive-subgroup condition.

The bounded sharp field below is an explicit published INPUT. It is not
proved from the coarse field, from CFSG, or from a finite catalogue here.
The adapter proves that this pair of published conclusions implies the
separately stated McIver--Neumann input. Existing inputs and endpoints
are unchanged.

CIRCULARITY WARNING: a future CFSG-only proof of this bundle must not
use the global McIver--Neumann consequence proved from this very bundle.
Tracey's published proof also uses small-degree computations; retaining
its conclusion as an input does not formalize those computations or
their completeness. This module consolidates logical dependencies only.
-/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

/-- The bounded sharp floor conclusion from Tracey 2018, Theorem 1.1(2).
No full-S3 guard is needed because its degree range starts at four. -/
def TraceyPublished2018BoundedSharpPermutationInput : Prop :=
  ∀ (n : ℕ), 4 ≤ n → n < 22 →
    ∀ J : Subgroup (Equiv.Perm (Fin n)),
      MulAction.IsPretransitive J (Fin n) →
        ∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧
          S.card ≤ TraceySharpHalfDegreeNumerics.sharpFloor n

/-- Optional stronger retention of the SAME published 2018 result.
Neither field is discharged in this module. -/
structure TraceyPublished2018PermutationInputBundle : Prop where
  coarse : TraceyPermutationGeneratorInput
  boundedSharp : TraceyPublished2018BoundedSharpPermutationInput

namespace TraceyPublished2018PermutationInputBundle

/-- Sharp floors pay every bounded transitive case; the already proved
degree-zero through degree-three bases retain the literal S3 exception. -/
theorem bounded_transitive
    (h : TraceyPublished2018PermutationInputBundle) :
    McIverNeumannFromTraceyBounded.BoundedTransitiveInput := by
  intro n hn J ht hJ
  by_cases hsmall : n ≤ 3
  · exact PermutationSmallDegreeOrdinaryGenerators.exists_half_degree_generators
      n J hsmall hJ
  · obtain ⟨S, hS, hc⟩ := h.boundedSharp n (by omega) hn J ht
    have hh := hc.trans (TraceySharpHalfDegreeNumerics.sharpFloor_le_half n (by omega))
    exact ⟨S, hS, by omega⟩

/-- The independent McIver--Neumann INPUT is redundant if both displayed
conclusions of Tracey 2018 are retained. This is not a CFSG-only theorem. -/
theorem mcIverNeumann
    (h : TraceyPublished2018PermutationInputBundle) :
    McIverNeumannPermutationGeneratorBound :=
  McIverNeumannFromTraceyBounded.mcIverNeumann_of_tracey_and_bounded_transitive
    h.coarse h.bounded_transitive

end TraceyPublished2018PermutationInputBundle
end SymmetricSubgroupAsymptotics
