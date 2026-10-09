import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopImporter

/-!
# Kernel-label form of the pair-relative character theorem

The relative-socle argument produces mixed labels which do not fit a single
`CharacterQuotientCertificate` mode: the prefix is labelled on the complete
source, while the relative positions are labelled on a binary Sylow source.
This file supplies the missing reusable counting bridge.

A `DegreeTwoPairRelativeLabelCertificate` records the finite combined label
used for one fixed quotient, proves that equal labels determine the original
epimorphism kernel, and proves the label-cardinality estimate at the exact
mixed profile slope.  The theorem `toQuotientEnvelope` then adds the target
automorphism fibre once.  `ofLabelCertificates` applies that theorem on every
literal normal quotient and constructs the universal lift data consumed by
the pair-top importer.

The remaining representation-theoretic task is now sharply stated: build
the kernel-determining label certificate from the prefix characters and the
relative socle characters.  No complete-source sum, numerical transfer, or
catalogue assembly remains after it.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- A finite mixed prefix/relative label on one fixed target quotient.
`labelCoefficient` contains only target-dependent choices (for example the
relative orbit/index factor), while the source-dependent growth is exactly
the displayed profile slope. -/
structure DegreeTwoPairRelativeLabelCertificate
    (Q : Type) [Group Q] [Finite Q]
    (profile : DegreeTwoPairRelativeProfile) : Type 1 where
  Label : (b : ℕ) → Subgroup (Equiv.Perm (Fin b)) → Type
  label_finite : ∀ b J, Finite (Label b J)
  label : ∀ (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))),
    GroupEpimorphism J Q → Label b J
  kernel_eq : ∀ (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b)))
      (f g : GroupEpimorphism J Q),
    label b J f = label b J g → f.1.ker = g.1.ker
  labelCoefficient : ℝ
  labelCoefficient_nonneg : 0 ≤ labelCoefficient
  label_card_bound : ∀ (b : ℕ)
      (J : Subgroup (Equiv.Perm (Fin b))),
    (Nat.card (Label b J) : ℝ) ≤
      labelCoefficient * (2 : ℝ) ^ (profile.slope * b)

namespace DegreeTwoPairRelativeLabelCertificate

variable {Q : Type} [Group Q] [Finite Q]
  {profile : DegreeTwoPairRelativeProfile}
  (C : DegreeTwoPairRelativeLabelCertificate Q profile)

/-- The combined relative label gives the exact quotient envelope.  The
automorphism factor is introduced here, once, by the literal kernel-fibre
theorem. -/
noncomputable def toQuotientEnvelope :
    DegreeTwoPairRelativeQuotientEnvelope Q profile where
  coefficient := C.labelCoefficient * (Nat.card (Q ≃* Q) : ℝ)
  coefficient_nonneg :=
    mul_nonneg C.labelCoefficient_nonneg (Nat.cast_nonneg _)
  bound := by
    intro b J
    letI : Finite (C.Label b J) := C.label_finite b J
    have hcard := groupEpimorphism_card_le_kernel_labels
      (C.label b J) (C.kernel_eq b J)
    have hcast : (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
        (Nat.card (C.Label b J) : ℝ) *
          (Nat.card (Q ≃* Q) : ℝ) := by
      exact_mod_cast hcard
    calc
      (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
          (Nat.card (C.Label b J) : ℝ) *
            (Nat.card (Q ≃* Q) : ℝ) := hcast
      _ ≤ (C.labelCoefficient *
            (2 : ℝ) ^ (profile.slope * b)) *
            (Nat.card (Q ≃* Q) : ℝ) :=
        mul_le_mul_of_nonneg_right (C.label_card_bound b J)
          (Nat.cast_nonneg _)
      _ = (C.labelCoefficient * (Nat.card (Q ≃* Q) : ℝ)) *
            (2 : ℝ) ^ (profile.slope * b) := by ring

end DegreeTwoPairRelativeLabelCertificate

namespace DegreeTwoPairRelativeLiftData

/-- Universal fixed-prefix/relative-tail lift theorem in the form required
by the finite catalogues.  Once every literal quotient has its combined
kernel label, this constructs all-original-normal lift data directly. -/
noncomputable def ofLabelCertificates
    {s : ℕ} {p : PreE7PairActionClass s}
    (profile :
      {N : Subgroup (preE7PairAction s p) // N.Normal} →
        DegreeTwoPairRelativeProfile)
    (capacity : ∀ N,
      (profile N).slope ≤ preE7CharacterWindow (2 * s))
    (certificate : ∀ N,
      DegreeTwoPairRelativeLabelCertificate
        (preE7PairAction s p ⧸ N.1) (profile N)) :
    DegreeTwoPairRelativeLiftData s p where
  profile := profile
  capacity := capacity
  envelope N := (certificate N).toQuotientEnvelope

end DegreeTwoPairRelativeLiftData

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
