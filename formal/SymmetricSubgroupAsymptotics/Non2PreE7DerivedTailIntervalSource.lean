import SymmetricSubgroupAsymptotics.Non2PreE7SmallAdditiveNumericalInstances
import SymmetricSubgroupAsymptotics.Non2PreE7SmallModelToolkit

/-!
# A quotient interval with a derived-head tail below it

This is the literal normal-axis adapter needed by small affine block cells.
Normals containing a fixed normal subgroup `E` are quotients of the faithful
action of `U / E`.  Every remaining normal is paid by a supplied cold tail.
The construction keeps the original action and every original normal axis;
it does not classify the ambient group by an abstract isomorphism label.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

private abbrev IntervalAxis {w : ℕ} (U : PreE7NonPairActionClass w) :=
  {N : Subgroup (preE7NonPairAction w U) // N.Normal}

/-- Structural and numerical data for one exact quotient interval.  Concrete
users normally obtain `tail_bound` from a quotient-specific
`DerivedHead.DerivedCyclicTarget`; the adapter deliberately accepts the
resulting bound rather than forgetting which quotient produced it. -/
structure PreE7DerivedTailIntervalSourceData
    (w : ℕ) (U : PreE7NonPairActionClass w) : Type where
  E : Subgroup (preE7NonPairAction w U)
  [E_normal : E.Normal]
  quotientDegree : ℕ
  quotientAction :
    (preE7NonPairAction w U ⧸ E) →* Equiv.Perm (Fin quotientDegree)
  quotientAction_injective : Function.Injective quotientAction
  theta : ℝ
  comparator_window : preE7CharacterRho * w ≤
    ((evenWidth w : ℝ) - ((max 2 quotientDegree : ℕ) : ℝ)) / 8
  tail_window : theta ≤ preE7CharacterWindow w
  tailCoefficient : IntervalAxis U → ℝ
  tailCoefficient_nonneg : ∀ N, 0 ≤ tailCoefficient N
  tail_bound : ∀ (N : IntervalAxis U), ¬ E ≤ N.1 →
    ∀ (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))),
      (Nat.card (GroupEpimorphism J
        (preE7NonPairAction w U ⧸ N.1)) : ℝ) ≤
        tailCoefficient N * (2 : ℝ) ^ (theta * b)
  main_total_bound : ∀ b,
    fusionAxisEnvelopeTotal (preE7NonPairAction w U)
        (fun N => if E ≤ N.1 then 1 else 0) ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)
  tail_total_bound : ∀ b,
    fusionAxisEnvelopeTotal (preE7NonPairAction w U)
        (fun N => if E ≤ N.1 then 0 else tailCoefficient N) ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)

attribute [instance] PreE7DerivedTailIntervalSourceData.E_normal

namespace PreE7DerivedTailIntervalSourceData

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  (D : PreE7DerivedTailIntervalSourceData w U)

/-- The exact certificate on one original normal axis. -/
def axis (N : IntervalAxis U) :
    PreE7SmallAxisCertificate (preE7NonPairAction w U) N
      (preE7NonPairAction w U ⧸ D.E) D.theta := by
  haveI : N.1.Normal := N.2
  by_cases hEN : D.E ≤ N.1
  · haveI : (N.1.map (QuotientGroup.mk' D.E)).Normal :=
      N.2.map _ (QuotientGroup.mk'_surjective D.E)
    exact .comparator
      ⟨N.1.map (QuotientGroup.mk' D.E), inferInstance⟩
      (quotientEquivOfKerLe (QuotientGroup.mk' D.E)
        (QuotientGroup.mk'_surjective D.E) N.1 (by
          simpa only [QuotientGroup.ker_mk'] using hEN))
  · exact .tail (D.tailCoefficient N) (D.tailCoefficient_nonneg N)
      (D.tail_bound N hEN)

@[simp] theorem axis_mainCoefficient (N : IntervalAxis U) :
    (D.axis N).mainCoefficient = if D.E ≤ N.1 then 1 else 0 := by
  by_cases hEN : D.E ≤ N.1 <;>
    simp [axis, hEN, PreE7SmallAxisCertificate.mainCoefficient]

@[simp] theorem axis_tailCoefficient (N : IntervalAxis U) :
    (D.axis N).tailCoefficient =
      if D.E ≤ N.1 then 0 else D.tailCoefficient N := by
  by_cases hEN : D.E ≤ N.1 <;>
    simp [axis, hEN, PreE7SmallAxisCertificate.tailCoefficient]

/-- The normal interval as the common small-additive source. -/
def additiveData : PreE7SmallAdditiveData w U where
  R := preE7NonPairAction w U ⧸ D.E
  degree := D.quotientDegree
  action := D.quotientAction
  action_injective := D.quotientAction_injective
  tailSlope := D.theta
  comparator_window := D.comparator_window
  tail_window := D.tail_window
  axis := D.axis

/-- The complete numerical package. -/
noncomputable def numericalData :
    PreE7SmallAdditiveNumericalData .acert w U where
  data := D.additiveData
  main_total_bound := by
    intro b
    change fusionAxisEnvelopeTotal (preE7NonPairAction w U)
      (fun N => (D.axis N).mainCoefficient) ≤ _
    simpa only [D.axis_mainCoefficient] using D.main_total_bound b
  tail_total_bound := by
    intro b
    change fusionAxisEnvelopeTotal (preE7NonPairAction w U)
      (fun N => (D.axis N).tailCoefficient) ≤ _
    simpa only [D.axis_tailCoefficient] using D.tail_total_bound b

/-- Final source at the construction boundary used by the primitive-affine
consumer. -/
noncomputable def toRankTailSourceOrYonedaTop :
    PreE7RankTailSourceOrYonedaTopData w U :=
  .inl (.ordinary .acert (.small D.numericalData))

end PreE7DerivedTailIntervalSourceData
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
