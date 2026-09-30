import SymmetricSubgroupAsymptotics.C3HighAlignedRefinedContinuation
import SymmetricSubgroupAsymptotics.C3HighAlignedRemainingConsumers
import SymmetricSubgroupAsymptotics.C3CompletePhysicalContinuation
import SymmetricSubgroupAsymptotics.C3TernaryPGroupAlignedPositiveLocal

/-!
# Every refined aligned high-C3 cell has a local row

After the degree-three ternary cells are removed, a transitive ternary
p-group cell has width nine or twenty seven: widths four, six and twelve are
even and cannot carry a transitive 3-group, so the positive-width
degree-nine and degree-twenty-seven ternary rows apply.

Together with the prime-base, natural-`A4`, degree-six and degree-twelve
rows, every refined cell reaches a nonnegative exponentially decaying row.
The high-C3 owner continuation, and with it the complete regular-C3 audit,
therefore close under the named ternary inputs and the Kovács--Praeger
abelianization bound.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- A transitive 3-group has odd degree. -/
theorem transitive_ternaryPGroup_width_not_even {w : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w))) [MulAction.IsPretransitive U (Fin w)]
    (hU : IsPGroup 3 U) (hw : 0 < w) : ¬ 2 ∣ w := by
  intro h2
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hU
  let x : Fin w := ⟨0, hw⟩
  have hdvd : w ∣ Nat.card U := by
    have h := Subgroup.index_dvd_card (MulAction.stabilizer U x)
    rwa [MulAction.index_stabilizer_of_transitive U x, Nat.card_fin] at h
  rw [hk] at hdvd
  have h3 : 2 ∣ 3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two (h2.trans hdvd)
  omega

/-- Every aligned ternary p-group cell of width other than three has a local
row: its width is nine or twenty seven, and the positive-width ternary rows
apply. -/
theorem c3HighAligned_ternaryPGroup_localRow
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (j : C3HighAlignedFirstOwnerIndex)
    (hk : c3PhysicalOwnerKindEquiv j.1.2.1 =
      C3PhysicalOwnerKind.ternaryPGroup)
    (hw : c3HighAlignedFirstOwnerWidth j ≠ 3) :
    C3HighAlignedLocalRow j := by
  rcases j with ⟨⟨d, owner, i⟩, hj⟩
  have hU := hj.2
  rw [hk] at hU
  letI := Non2TransitiveActionClass.representative_pretransitive i
  cases d with
  | three => exact absurd rfl hw
  | four =>
      let U : Subgroup (Equiv.Perm (Fin 4)) := i.representative
      letI : MulAction.IsPretransitive U (Fin 4) :=
        Non2TransitiveActionClass.representative_pretransitive i
      exact absurd (by decide : 2 ∣ 4)
        (transitive_ternaryPGroup_width_not_even U hU (by decide))
  | six =>
      let U : Subgroup (Equiv.Perm (Fin 6)) := i.representative
      letI : MulAction.IsPretransitive U (Fin 6) :=
        Non2TransitiveActionClass.representative_pretransitive i
      exact absurd (by decide : 2 ∣ 6)
        (transitive_ternaryPGroup_width_not_even U hU (by decide))
  | twelve =>
      let U : Subgroup (Equiv.Perm (Fin 12)) := i.representative
      letI : MulAction.IsPretransitive U (Fin 12) :=
        Non2TransitiveActionClass.representative_pretransitive i
      exact absurd (by decide : 2 ∣ 12)
        (transitive_ternaryPGroup_width_not_even U hU (by decide))
  | nine =>
      exact c3HighAligned_degreeNine_ternaryPGroup_localRow hChief hPrimitive h18
        ⟨⟨C3HighWidthLabel.nine, owner, i⟩, hj⟩ hk rfl
  | twentySeven =>
      exact c3HighAligned_degreeTwentySeven_ternaryPGroup_localRow
        ⟨⟨C3HighWidthLabel.twentySeven, owner, i⟩, hj⟩ hk rfl

/-- Exhaustion: every refined aligned cell reaches one of the ternary
p-group, natural-`A4`, degree-six, prime-base or binary-nine rows. -/
theorem c3HighRefinedAligned_localRow
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (j : C3HighRefinedAlignedIndex) :
    C3HighAlignedLocalRow j.1 := by
  obtain ⟨j, hj⟩ := j
  cases hk : c3PhysicalOwnerKindEquiv j.1.2.1 with
  | ternaryPGroup =>
      exact c3HighAligned_ternaryPGroup_localRow hChief hPrimitive h18 j hk
        (fun hw => hj ⟨hw, hk⟩)
  | naturalA4 => exact c3HighAligned_naturalA4_localRow j hk
  | degreeSix =>
      obtain ⟨D, hD, h⟩ := c3HighAligned_degreeSix_local_bound hPrimitive hKP j hk
      exact C3HighAlignedLocalRow.of_kernel j .degreeSix D hD h
  | degreeTwelve =>
      obtain ⟨r, D, hD, h⟩ :=
        c3HighAligned_degreeTwelve_local_bound hChief hWeight hPrimitive h18 j hk
      exact C3HighAlignedLocalRow.of_kernel j r D hD h

/-- The complete high-C3 structural-owner continuation, with no remaining
local-row hypothesis. -/
noncomputable def c3PhysicalStructuralOwner_closedExponentialForwardEstimate
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      c3PhysicalStructuralOwnerRatio :=
  let hrow := c3HighRefinedAligned_localRow hChief hWeight hPrimitive h18 hKP
  c3PhysicalStructuralOwner_refinedExponentialForwardEstimate
    hChief hWeight hPrimitive h18
    (fun j => Classical.choose (hrow j))
    (fun j => (Classical.choose_spec (hrow j)).1)
    (fun j => (Classical.choose_spec (hrow j)).2.1)
    (fun j => (Classical.choose_spec (hrow j)).2.2)

/-- The complete regular-C3 ordinary audit: the closed high-owner
continuation together with the closed residual row. -/
noncomputable def c3CompleteOrdinary_closedExponentialForwardEstimate
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      c3CompleteOrdinaryRatio :=
  OrdinaryFrontierClosure.ExponentialForwardEstimate.of_le
    (OrdinaryFrontierClosure.ExponentialForwardEstimate.add
      (c3PhysicalStructuralOwner_closedExponentialForwardEstimate
        hChief hWeight hPrimitive h18 hKP)
      (c3FinalResidual_exponentialForwardEstimate hChief hWeight hPrimitive h18))
    3 c3CompleteOrdinaryRatio_le_owner_add_residual

end SymmetricSubgroupAsymptotics

end
