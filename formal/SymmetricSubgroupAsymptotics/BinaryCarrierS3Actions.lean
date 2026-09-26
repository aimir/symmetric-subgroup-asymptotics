import SymmetricSubgroupAsymptotics.OddCriticalProfiles
import SymmetricSubgroupAsymptotics.BinaryCarrierSmallSupportPhysical

/-! Original physical profiles with one natural S3 marker and the full
thirteen-colour binary alphabet. The marker keeps its own three points,
normalizer six and multiplicity one. No contracted C2 divisor is used. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierS3Actions

abbrev Target := BinaryCarrierOriginalCyclicFourHall.Target

def points : OddCriticalActionKind ⊕ Target → Type
  | .inl i => oddCriticalActionPoints i
  | .inr t => BinaryCarrierOriginalCyclicFourHall.points t

instance (i : OddCriticalActionKind ⊕ Target) : Fintype (points i) := by
  cases i <;> dsimp [points] <;> infer_instance

instance (i : OddCriticalActionKind ⊕ Target) : Nonempty (points i) := by
  cases i <;> dsimp [points] <;> infer_instance

def action : (i : OddCriticalActionKind ⊕ Target) → Subgroup (Equiv.Perm (points i))
  | .inl i => oddCriticalActionSubgroup i
  | .inr t => BinaryCarrierOriginalCyclicFourHall.action t

def multiplicity (p : CriticalProfile) (q : Target → ℕ) :
    OddCriticalActionKind ⊕ Target → ℕ := Sum.elim (oddCriticalMultiplicity true p) q

abbrev ModelPoints (p : CriticalProfile) (q : Target → ℕ) :=
  OrbitProfilePoints points (multiplicity p q)

abbrev ModelFamily (p : CriticalProfile) (q : Target → ℕ) :=
  {H : Subgroup (Equiv.Perm (ModelPoints p q)) // OrbitProfileFull action 1 H}

def originalDenominator (p : CriticalProfile) (q : Target → ℕ) : ℝ :=
  ∏ i, (Nat.card (Subgroup.normalizer (action i : Set (Equiv.Perm (points i)))) : ℝ) ^
    multiplicity p q i * (multiplicity p q i).factorial

/-- The old binary profile remains on the original support; S3 adds three
physical points even though its contraction adds one binary coordinate. -/
theorem physicalDegree (p : CriticalProfile) (q : Target → ℕ) :
    ∑ i, multiplicity p q i * Fintype.card (points i) =
      2*(p.rank + BinaryCarrierSmallSupportProfiles.support q)+3 := by
  rw [Fintype.sum_sum_type]
  change (∑ i, oddCriticalMultiplicity true p i * Fintype.card (oddCriticalActionPoints i)) +
    (∑ t, q t * Fintype.card (BinaryCarrierOriginalCyclicFourHall.points t)) = _
  rw [oddCriticalMultiplicity_degree]
  have htail := BinaryCarrierOriginalSmallSupport.tailPoints_card
    (q none) (fun t => q (some t))
  simp only [BinaryCarrierOriginalSmallSupport.TailPoints, OrbitProfilePoints,
    Nat.card_eq_fintype_card, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin,
    BinaryCarrierSmallSupportProfiles.multiplicity_split] at htail
  change (∑ t, q t * Fintype.card (BinaryCarrierOriginalCyclicFourHall.points t)) =
    2*BinaryCarrierSmallSupportProfiles.support q at htail
  rw [htail]
  simp only [ite_true]
  omega

/-- Exactly six times the original binary denominator, including all
unchanged original carrier normalizers and occurrence factorials. -/
theorem originalDenominator_eq (p : CriticalProfile) (q : Target → ℕ) :
    originalDenominator p q = 6 * BinaryCarrierMixedProfile.originalDenominator
      BinaryCarrierOriginalCyclicFourHall.points BinaryCarrierOriginalCyclicFourHall.action p q := by
  have ho : (∏ i, (Nat.card (Subgroup.normalizer (oddCriticalActionSubgroup i :
      Set (Equiv.Perm (oddCriticalActionPoints i)))) : ℝ) ^ oddCriticalMultiplicity true p i *
        (oddCriticalMultiplicity true p i).factorial)⁻¹ = (p.weight : ℝ)/6 := by
    have h := congrArg (fun r : ℚ => (r : ℝ)) (oddCriticalMultiplicity_weight true p)
    push_cast at h
    simpa only [ite_true] using h
  have hc : (∏ i, (Nat.card (Subgroup.normalizer (criticalActionSubgroup i :
      Set (Equiv.Perm (criticalActionPoints i)))) : ℝ) ^ p.multiplicity i *
        (p.multiplicity i).factorial)⁻¹ = (p.weight : ℝ) := by
    have h := congrArg (fun r : ℚ => (r : ℝ)) p.original_normalizer_weight
    push_cast at h
    exact h
  have hparts : (∏ i, (Nat.card (Subgroup.normalizer (oddCriticalActionSubgroup i :
      Set (Equiv.Perm (oddCriticalActionPoints i)))) : ℝ) ^ oddCriticalMultiplicity true p i *
        (oddCriticalMultiplicity true p i).factorial) =
      6 * (∏ i, (Nat.card (Subgroup.normalizer (criticalActionSubgroup i :
        Set (Equiv.Perm (criticalActionPoints i)))) : ℝ) ^ p.multiplicity i *
          (p.multiplicity i).factorial) := by
    apply inv_inj.mp
    rw [ho, mul_inv_rev, hc]
    ring
  unfold originalDenominator BinaryCarrierMixedProfile.originalDenominator
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  change (∏ i, (Nat.card (Subgroup.normalizer (oddCriticalActionSubgroup i :
      Set (Equiv.Perm (oddCriticalActionPoints i)))) : ℝ) ^ oddCriticalMultiplicity true p i *
        (oddCriticalMultiplicity true p i).factorial) * _ = _
  rw [hparts]
  simp only [action, multiplicity, BinaryCarrierMixedProfile.action,
    BinaryCarrierMixedProfile.multiplicity, Sum.elim_inl, Sum.elim_inr]
  ring <;> rfl

end SymmetricSubgroupAsymptotics.BinaryCarrierS3Actions
