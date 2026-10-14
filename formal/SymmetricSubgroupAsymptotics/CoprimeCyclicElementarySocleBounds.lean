import SymmetricSubgroupAsymptotics.CoprimeCyclicQuotientSocleBounds
import SymmetricSubgroupAsymptotics.CoprimeCyclicElementarySocles

/-!
# Positive quotient-socle bounds from an actual elementary kernel module

An actual `t`-generator conjugation module of coprime quotient order has
the same generator bound on all invariant subspaces, by Maschke. The
normal-generator bridge and prime-type sharing then give the bound `t`
on every original quotient socle, for positive `t`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics
namespace CoprimeCyclicElementarySocleBounds

variable {G : Type} [Group G] [Finite G]
  (E : Subgroup G) [E.Normal] (C : ElementaryMinimalNormalChart E)

theorem kernel_normalGen_le
    (hcop : Nat.Coprime C.p (Nat.card (G ⧸ E)))
    (t : ℕ) (hgen : RepresentationGeneratedBy C.quotientRepresentation.ρ t)
    (H : Subgroup G) [H.Normal] (hHE : H ≤ E) :
    MarkedC4.normalGen H ≤ t := by
  letI : NeZero (Nat.card (G ⧸ E) : ZMod C.p) := ⟨by
    intro hzero
    exact (C.p_prime.coprime_iff_not_dvd.mp hcop)
      ((ZMod.natCast_eq_zero_iff _ _).mp hzero)⟩
  have huniform := RepresentationGeneratedBy.uniform_of_invertible_order
    C.quotientRepresentation.ρ hgen
  exact normalGen_le_of_elementaryNormalSubrepresentation_generated E C H hHE t
    (huniform (C.originalKernelChart.normalSubrepresentation
      (QuotientGroup.mk' E) (QuotientGroup.mk'_surjective E)
      C.quotientRepresentation H))

theorem of_surjective [IsCyclic (G ⧸ E)]
    (hcop : Nat.Coprime C.p (Nat.card (G ⧸ E)))
    (t : ℕ) (ht : 1 ≤ t)
    (hgen : RepresentationGeneratedBy C.quotientRepresentation.ρ t)
    {Q : Type} [Group Q] (pi : G →* Q) (hpi : Function.Surjective pi) :
    SocleNormalGeneratorBound Q t := by
  apply CoprimeCyclicQuotientSocleBounds.quotientSocle_of_kernel C.p E
    (CoprimeCyclicElementarySocles.kernel_isPGroup E C) hcop t ht ?_ pi hpi
  intro H hH hHE
  letI := hH
  exact kernel_normalGen_le E C hcop t hgen H hHE

theorem quotient [IsCyclic (G ⧸ E)]
    (hcop : Nat.Coprime C.p (Nat.card (G ⧸ E)))
    (t : ℕ) (ht : 1 ≤ t)
    (hgen : RepresentationGeneratedBy C.quotientRepresentation.ρ t)
    (N : Subgroup G) [N.Normal] : SocleNormalGeneratorBound (G ⧸ N) t :=
  of_surjective E C hcop t ht hgen
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

end CoprimeCyclicElementarySocleBounds
end SymmetricSubgroupAsymptotics

end
