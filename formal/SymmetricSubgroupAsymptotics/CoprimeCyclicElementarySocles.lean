import SymmetricSubgroupAsymptotics.CoprimeCyclicQuotientSocles
import SymmetricSubgroupAsymptotics.ElementaryNormalModuleGenerators
import SymmetricSubgroupAsymptotics.RepresentationGeneratorRestrictionMaschke

/-!
# Every quotient socle is cyclic for a cyclic coprime elementary extension

The actual elementary kernel chart carries its ambient conjugation module.
If this module is cyclic and the quotient is cyclic of order coprime to
the kernel prime, Maschke supplies a cyclic generator for every invariant
subspace. The checked elementary-chart bridge turns this into one ambient
normal generator for every normal subgroup inside the kernel. The generic
prime-type sharing argument then treats every actual surjective quotient.

The input is a generator theorem on the displayed kernel representation,
not an assumption about the socles of the eventual quotients.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics
namespace CoprimeCyclicElementarySocles

variable {G : Type} [Group G] [Finite G]
  (E : Subgroup G) [E.Normal] (C : ElementaryMinimalNormalChart E)

theorem kernel_isPGroup : IsPGroup C.p E :=
  (ZModModule.isPGroup_multiplicative (n := C.p) (G := C.V)).of_injective
    C.equiv.toMonoidHom C.equiv.injective

theorem kernel_normalGen_le_one
    (hcop : Nat.Coprime C.p (Nat.card (G ⧸ E)))
    (hcyclic : RepresentationGeneratedBy C.quotientRepresentation.ρ 1)
    (H : Subgroup G) [H.Normal] (hHE : H ≤ E) :
    MarkedC4.normalGen H ≤ 1 := by
  letI : NeZero (Nat.card (G ⧸ E) : ZMod C.p) := ⟨by
    intro hzero
    exact (C.p_prime.coprime_iff_not_dvd.mp hcop)
      ((ZMod.natCast_eq_zero_iff _ _).mp hzero)⟩
  have huniform := RepresentationGeneratedBy.uniform_of_invertible_order
    C.quotientRepresentation.ρ hcyclic
  exact normalGen_le_of_elementaryNormalSubrepresentation_generated E C H hHE 1
    (huniform (C.originalKernelChart.normalSubrepresentation
      (QuotientGroup.mk' E) (QuotientGroup.mk'_surjective E)
      C.quotientRepresentation H))

/-- The same original elementary module controls every displayed
surjective image, including quotients that no longer retain a complement. -/
theorem of_surjective [IsCyclic (G ⧸ E)]
    (hcop : Nat.Coprime C.p (Nat.card (G ⧸ E)))
    (hcyclic : RepresentationGeneratedBy C.quotientRepresentation.ρ 1)
    {Q : Type} [Group Q] (pi : G →* Q) (hpi : Function.Surjective pi) :
    SocleNormalGeneratorBound Q 1 := by
  apply CoprimeCyclicQuotientSocles.quotientSocle_of_kernel C.p E
    (kernel_isPGroup E C) hcop ?_ pi hpi
  intro H hH hHE
  letI := hH
  exact kernel_normalGen_le_one E C hcop hcyclic H hHE

/-- Every original normal denominator is retained literally. -/
theorem quotient [IsCyclic (G ⧸ E)]
    (hcop : Nat.Coprime C.p (Nat.card (G ⧸ E)))
    (hcyclic : RepresentationGeneratedBy C.quotientRepresentation.ρ 1)
    (N : Subgroup G) [N.Normal] : SocleNormalGeneratorBound (G ⧸ N) 1 :=
  of_surjective E C hcop hcyclic (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

end CoprimeCyclicElementarySocles
end SymmetricSubgroupAsymptotics

end
