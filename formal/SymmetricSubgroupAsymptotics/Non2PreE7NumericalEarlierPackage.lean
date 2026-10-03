import SymmetricSubgroupAsymptotics.Non2PreE7ExceptionalCatalogue
import SymmetricSubgroupAsymptotics.Non2PreE7CharacterCertificateTemplate
import SymmetricSubgroupAsymptotics.AffineComponentWidthCost

/-!
# Numerically complete earlier-owner packages

The mixed physical catalogue needs more than a local counting inequality.
For every accepted original action it must retain the transfer parameters
and uniform totals of both coefficient rows.  This structure is the exact
bridge from a family template to the all-width catalogue aggregation.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- A physical earlier-owner package with every numerical fact used by the
global additive exceptional transfer. -/
structure PreE7EarlierNumericalPackage
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (w : ℕ) (i : PreE7NonPairActionClass w) where
  package : PreE7EarlierLocalPackage family w i
  parameters : PreE7CharacterEntryParameters preE7CharacterRho w
    package.certificate.v package.certificate.eta package.certificate.delta
    package.certificate.cutoff package.certificate.alpha
    package.certificate.theta
  main_total_growth :
    (∀ b, package.certificate.D b ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)) ∨
    ((w ≤ 1024 ∧ ∃ K : ℝ, ∃ p : ℕ, 0 ≤ K ∧ ∀ b,
      package.certificate.D b ≤ K * (1 + (b : ℝ)) ^ p) ∨
    (∀ b, package.certificate.D b ≤
      (2 : ℝ) ^
        (PrimitiveAffineImprimitiveBlockTransfer.affineComponentWidthCost w +
          8 * (w : ℝ) * Real.logb 2 (b + 1))))
  tail_total_bound : ∀ b,
    package.certificate.T b ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)

/-- The numerically certified family predicate used by the final catalogue.
It is still an existential predicate on the literal original action; the
witness now contains the global summability data as well as the local row. -/
def preE7NoPairNoC3EarlierNumericalFamilyAction
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (w : ℕ) (i : PreE7NonPairActionClass w) : Prop :=
  Nonempty (PreE7EarlierNumericalPackage family w i)

/-- Package an ordinary comparator certificate once its entry parameters and
the two literal-axis totals have been proved. -/
noncomputable def PreE7EarlierNumericalPackage.ofComparator
    {family : PreE7NoPairNoC3EarlierOwnerFamily}
    {w : ℕ} {i : PreE7NonPairActionClass w}
    (C : PreE7EarlierActionComparatorCertificate family w i)
    (parameters : PreE7CharacterEntryParameters preE7CharacterRho w
      C.v C.eta C.delta C.cutoff C.alpha C.theta)
    (main_total_bound : ∀ b,
      fusionAxisEnvelopeTotal (preE7NonPairAction w i) (C.C b) ≤
        (2 : ℝ) ^
          (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2))
    (tail_total_bound : ∀ b,
      fusionAxisEnvelopeTotal (preE7NonPairAction w i)
          (C.tailCoefficient b) ≤
        (2 : ℝ) ^
          (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)) :
    PreE7EarlierNumericalPackage family w i where
  package := .ofComparator C
  parameters := parameters
  main_total_growth := .inl main_total_bound
  tail_total_bound := tail_total_bound

/-- Polynomial main rows are permitted only on the fixed bounded-width
part of the menu.  Their finitely many constants are absorbed by the global
menu theorem rather than by a false pointwise normalization to coefficient
one. -/
noncomputable def PreE7EarlierNumericalPackage.ofPolynomialComparator
    {family : PreE7NoPairNoC3EarlierOwnerFamily}
    {w : ℕ} {i : PreE7NonPairActionClass w}
    (C : PreE7EarlierActionComparatorCertificate family w i)
    (parameters : PreE7CharacterEntryParameters preE7CharacterRho w
      C.v C.eta C.delta C.cutoff C.alpha C.theta)
    (width_upper : w ≤ 1024)
    (main_total_polynomial : ∃ K : ℝ, ∃ p : ℕ, 0 ≤ K ∧ ∀ b,
      fusionAxisEnvelopeTotal (preE7NonPairAction w i) (C.C b) ≤
        K * (1 + (b : ℝ)) ^ p)
    (tail_total_bound : ∀ b,
      fusionAxisEnvelopeTotal (preE7NonPairAction w i)
          (C.tailCoefficient b) ≤
        (2 : ℝ) ^
          (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)) :
    PreE7EarlierNumericalPackage family w i where
  package := .ofComparator C
  parameters := parameters
  main_total_growth := .inr (.inl ⟨width_upper, main_total_polynomial⟩)
  tail_total_bound := tail_total_bound

/-- Package a complete-source certificate whose finite coefficient has the
standard imprimitive-affine width cost.  The global menu theorem, rather
than a false per-action logarithmic normalization, absorbs that cost. -/
noncomputable def PreE7EarlierNumericalPackage.ofAffinePackage
    {family : PreE7NoPairNoC3EarlierOwnerFamily}
    {w : ℕ} {i : PreE7NonPairActionClass w}
    (package : PreE7EarlierLocalPackage family w i)
    (parameters : PreE7CharacterEntryParameters preE7CharacterRho w
      package.certificate.v package.certificate.eta
      package.certificate.delta package.certificate.cutoff
      package.certificate.alpha package.certificate.theta)
    (main_total_affine : ∀ b, package.certificate.D b ≤
      (2 : ℝ) ^
        (PrimitiveAffineImprimitiveBlockTransfer.affineComponentWidthCost w +
          8 * (w : ℝ) * Real.logb 2 (b + 1)))
    (tail_total_bound : ∀ b,
      package.certificate.T b ≤
        (2 : ℝ) ^
          (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)) :
    PreE7EarlierNumericalPackage family w i where
  package := package
  parameters := parameters
  main_total_growth := .inr (.inr main_total_affine)
  tail_total_bound := tail_total_bound

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
