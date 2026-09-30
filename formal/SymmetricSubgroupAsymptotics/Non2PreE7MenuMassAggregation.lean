import SymmetricSubgroupAsymptotics.GrowingMenuMassEntryCertificate
import SymmetricSubgroupAsymptotics.Non2PreE7ConcreteInterface

/-!
# Complete original-weight menu aggregation for the pre-E7 frontier

The published labelled transitive-subgroup count controls the number of
restricted pre-E7 action classes.  A fixed first-owner menu changes that
count by only a fixed factor.  Combining this fact with a uniform bound for
one complete axis-envelope entry proves the exact original-normalizer-weighted
mass required by `PreE7NumericalCertificate`.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical Pointwise

namespace SymmetricSubgroupAsymptotics

/-- Literal labelled transitive subgroups of the symmetric group on `w`
points.  No quotient by conjugacy is taken in this published counting input. -/
abbrev LabelledTransitiveSubgroup (w : ℕ) :=
  {U : Subgroup (Equiv.Perm (Fin w)) //
    MulAction.IsPretransitive U (Fin w)}

/-- **Published input LIT-TRANSITIVE-COUNT.** Lucchini--Menegazzo--Morigi,
*Asymptotic results for transitive permutation groups*, Bull. London Math.
Soc. 32 (2000), 191--195.  The labelled consequence is stated explicitly in
Roney-Dougal--Tracey (2025), version 1, introduction, p. 2: the number is at
most `2^(b*w^2/sqrt(log w))` for an absolute constant `b`.  We record exactly
the weaker subquadratic consequence used by the menu aggregation. -/
def LucchiniMenegazzoMorigiTransitiveCountInput : Prop :=
  SubquadraticMenuIndexCount LabelledTransitiveSubgroup

namespace Non2UnipotentPrefixFiniteMenu

open RepeatedMarkerOwnerBound

private def non2ActionToLabelled (w : ℕ) :
    Non2TransitiveAction (Fin w) → LabelledTransitiveSubgroup w :=
  fun U => ⟨U.1, U.2.2⟩

private theorem non2ActionToLabelled_injective (w : ℕ) :
    Function.Injective (non2ActionToLabelled w) := by
  intro U V h
  exact Subtype.ext
    (congrArg (fun X : LabelledTransitiveSubgroup w => X.1) h)

/-- Restricting to non-2 actions, quotienting by original ambient conjugacy,
and finally imposing the pre-E7 no-frame predicate can only decrease the
labelled transitive-subgroup count. -/
theorem preE7ActionClass_card_le_labelled (w : ℕ) :
    Nat.card (PreE7ActionClass w) ≤
      Nat.card (LabelledTransitiveSubgroup w) := by
  calc
    Nat.card (PreE7ActionClass w) ≤
        Nat.card (Non2TransitiveActionClass (Fin w)) :=
      Finite.card_subtype_le _
    _ ≤ Nat.card (Non2TransitiveAction (Fin w)) := by
      exact Nat.card_le_card_of_surjective
        (fun U : Non2TransitiveAction (Fin w) =>
          Quotient.mk (non2TransitiveActionSetoid (Fin w)) U)
        Quotient.mk_surjective
    _ ≤ Nat.card (LabelledTransitiveSubgroup w) :=
      Nat.card_le_card_of_injective
        (non2ActionToLabelled w) (non2ActionToLabelled_injective w)

/-- The fixed first-owner label adds only the factor `r+1`; hence the exact
pre-E7 owner/action index inherits the published subquadratic count. -/
theorem preE7FirstOwnerIndex_subquadratic
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput) (r : ℕ) :
    SubquadraticMenuIndexCount
      (fun w => PreE7FirstOwnerIndex (r + 1) w) := by
  intro ε hε
  obtain ⟨B, hB, hcount⟩ := hLMM ε hε
  refine ⟨((r + 1 : ℕ) : ℝ) * B, mul_nonneg (by positivity) hB, ?_⟩
  intro w
  have hpre : (Nat.card (PreE7ActionClass w) : ℝ) ≤
      (Nat.card (LabelledTransitiveSubgroup w) : ℝ) := by
    exact_mod_cast preE7ActionClass_card_le_labelled w
  calc
    (Nat.card (PreE7FirstOwnerIndex (r + 1) w) : ℝ) =
        ((r + 1 : ℕ) : ℝ) * (Nat.card (PreE7ActionClass w) : ℝ) := by
      simp only [PreE7FirstOwnerIndex, Nat.card_prod, Nat.card_fin,
        Nat.cast_mul]
    _ ≤ ((r + 1 : ℕ) : ℝ) *
        (Nat.card (LabelledTransitiveSubgroup w) : ℝ) :=
      mul_le_mul_of_nonneg_left hpre (by positivity)
    _ ≤ ((r + 1 : ℕ) : ℝ) *
        (B * (2 : ℝ) ^ (ε * (w : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left (hcount w) (by positivity)
    _ = (((r + 1 : ℕ) : ℝ) * B) *
        (2 : ℝ) ^ (ε * (w : ℝ) ^ 2) := by ring

/-- The exact complete axis-envelope entry divided by its original action
normalizer.  This abbreviation prevents a consumer from silently changing
either the literal normal-axis sum or the action weight. -/
abbrev preE7WeightedAxisEntry {r : ℕ}
    (D : PreE7OwnerComparatorData r)
    (w : ℕ) (i : PreE7FirstOwnerIndex (r + 1) w) (b : ℕ) : ℝ :=
  fusionAxisEnvelopeTotal
      (preE7FirstOwnerAction w i)
      (fusionOwnerCapacityCoefficient b
        (preE7FirstOwnerAction w i)
        (D.Owned w i b) (D.C w i b) (D.eta w i)) /
    (Nat.card (Subgroup.normalizer
      (preE7FirstOwnerAction w i :
        Set (Equiv.Perm (Fin w)))) : ℝ)

/-- The remaining action consumers need only prove this one-entry estimate.
All action-class, fixed-owner and finite-width aggregation is discharged by
`preE7PolynomialSubquadraticMenuMassBound`. -/
def PreE7PolynomialSubquadraticEntryMassBound {r : ℕ}
    (D : PreE7OwnerComparatorData r) : Prop :=
  PolynomialSubquadraticMenuEntryBound 3
    (fun w i b => fusionAxisEnvelopeTotal
      (preE7FirstOwnerAction w i)
      (fusionOwnerCapacityCoefficient b
        (preE7FirstOwnerAction w i)
        (D.Owned w i b) (D.C w i b) (D.eta w i)))
    (fun w i =>
      (Nat.card (Subgroup.normalizer
        (preE7FirstOwnerAction w i :
          Set (Equiv.Perm (Fin w)))) : ℝ))

/-- An even simpler consumer-facing target before division by the original
normalizer.  Since every normalizer contains the identity, this numerator
bound implies `PreE7PolynomialSubquadraticEntryMassBound`. -/
def PreE7PolynomialSubquadraticAxisEnvelopeBound {r : ℕ}
    (D : PreE7OwnerComparatorData r) : Prop :=
  PolynomialSubquadraticMenuNumeratorBound 3
    (fun w i b => fusionAxisEnvelopeTotal
      (preE7FirstOwnerAction w i)
      (fusionOwnerCapacityCoefficient b
        (preE7FirstOwnerAction w i)
        (D.Owned w i b) (D.C w i b) (D.eta w i)))

theorem preE7EntryMassBound_of_axisEnvelopeBound
    {r : ℕ} (D : PreE7OwnerComparatorData r)
    (haxis : PreE7PolynomialSubquadraticAxisEnvelopeBound D) :
    PreE7PolynomialSubquadraticEntryMassBound D := by
  apply polynomialSubquadraticMenuEntryBound_of_numerator _ _
  · intro w i b
    apply fusionAxisEnvelopeTotal_nonneg
    intro N
    exact fusionOwnerCapacityCoefficient_nonneg
      (preE7FirstOwnerAction w i) (D.Owned w i b) (D.C w i b)
      (D.eta w i) (D.coefficient_nonneg w i b) N
  · intro w i
    exact_mod_cast (Nat.card_pos (α :=
      Subgroup.normalizer
        (preE7FirstOwnerAction w i : Set (Equiv.Perm (Fin w)))))
  · exact haxis

/-- Complete pre-E7 menu-mass aggregation.  It preserves the literal action,
all literal normal axes, the owner-or-capacity coefficient and the original
normalizer divisor. -/
theorem preE7PolynomialSubquadraticMenuMassBound
    {r : ℕ} (D : PreE7OwnerComparatorData r)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hentry : PreE7PolynomialSubquadraticEntryMassBound D) :
    PolynomialSubquadraticMenuMassBound 3
      (fun w i b => fusionAxisEnvelopeTotal
        (preE7FirstOwnerAction w i)
        (fusionOwnerCapacityCoefficient b
          (preE7FirstOwnerAction w i)
          (D.Owned w i b) (D.C w i b) (D.eta w i)))
      (fun w i =>
        (Nat.card (Subgroup.normalizer
          (preE7FirstOwnerAction w i :
            Set (Equiv.Perm (Fin w)))) : ℝ)) :=
  polynomialSubquadraticMenuMassBound_of_index_entry _ _
    (preE7FirstOwnerIndex_subquadratic hLMM r) hentry

/-- Complete aggregation directly from an unweighted axis-envelope bound.
The original normalizer remains in the resulting mass even though the proof
uses only its elementary lower bound by one. -/
theorem preE7PolynomialSubquadraticMenuMassBound_of_axisEnvelope
    {r : ℕ} (D : PreE7OwnerComparatorData r)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (haxis : PreE7PolynomialSubquadraticAxisEnvelopeBound D) :
    PolynomialSubquadraticMenuMassBound 3
      (fun w i b => fusionAxisEnvelopeTotal
        (preE7FirstOwnerAction w i)
        (fusionOwnerCapacityCoefficient b
          (preE7FirstOwnerAction w i)
          (D.Owned w i b) (D.C w i b) (D.eta w i)))
      (fun w i =>
        (Nat.card (Subgroup.normalizer
          (preE7FirstOwnerAction w i :
            Set (Equiv.Perm (Fin w)))) : ℝ)) :=
  preE7PolynomialSubquadraticMenuMassBound D hLMM
    (preE7EntryMassBound_of_axisEnvelopeBound D haxis)

/-- Constructor for the numerical package after the action consumers prove
the one-entry mass estimate and the already separate parameter inequalities. -/
noncomputable def PreE7NumericalCertificate.ofEntryMass
    {r : ℕ} (D : PreE7OwnerComparatorData r)
    (rho : ℝ) (rho_pos : 0 < rho) (rho_le_eighth : rho ≤ 1 / 8)
    (parameters : GrowingQuotientParameterBound rho
      D.v D.eta D.delta D.cutoff D.alpha)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hentry : PreE7PolynomialSubquadraticEntryMassBound D) :
    PreE7NumericalCertificate D where
  rho := rho
  rho_pos := rho_pos
  rho_le_eighth := rho_le_eighth
  parameters := parameters
  menuMass := preE7PolynomialSubquadraticMenuMassBound D hLMM hentry

/-- Numerical package constructor from the unweighted axis-envelope estimate.
This is the shortest endpoint for branch-local action consumers. -/
noncomputable def PreE7NumericalCertificate.ofAxisEnvelope
    {r : ℕ} (D : PreE7OwnerComparatorData r)
    (rho : ℝ) (rho_pos : 0 < rho) (rho_le_eighth : rho ≤ 1 / 8)
    (parameters : GrowingQuotientParameterBound rho
      D.v D.eta D.delta D.cutoff D.alpha)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (haxis : PreE7PolynomialSubquadraticAxisEnvelopeBound D) :
    PreE7NumericalCertificate D :=
  PreE7NumericalCertificate.ofEntryMass D rho rho_pos rho_le_eighth
    parameters hLMM (preE7EntryMassBound_of_axisEnvelopeBound D haxis)

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
