import SymmetricSubgroupAsymptotics.CFSGSymplecticFirstPairTailEquiv
import Mathlib.GroupTheory.GroupAction.Quotient

/-! The same elementary group acts transitively on actual ordered
hyperbolic pairs. Its actual stabilizer is the smaller elementary group,
so orbit-stabilizer supplies an exact order recurrence. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticStabilizerCoordinates
open CFSGSymplecticSerreMatrices CFSGSymplecticTransvectionGeometry
variable (K : Type) [Field K]

abbrev HyperbolicPairs (n : ℕ) :=
  {p : (Index n → K) × (Index n → K) // pairing n p.1 p.2 = 1}

instance hyperbolicPairAction (n : ℕ) :
    MulAction (elementaryRootGroup K n) (HyperbolicPairs K n) where
  smul g p := ⟨((g.val : Mat K n) *ᵥ p.val.1, (g.val : Mat K n) *ᵥ p.val.2),
    (elementary_preserves_pairing n g p.val.1 p.val.2).trans p.property⟩
  one_smul p := by
    apply Subtype.ext
    exact Prod.ext (Matrix.one_mulVec _) (Matrix.one_mulVec _)
  mul_smul g h p := by
    apply Subtype.ext
    apply Prod.ext
    · exact (Matrix.mulVec_mulVec p.val.1 (g.val : Mat K n) (h.val : Mat K n)).symm
    · exact (Matrix.mulVec_mulVec p.val.2 (g.val : Mat K n) (h.val : Mat K n)).symm

def standardHyperbolicPair (r : ℕ) : HyperbolicPairs K (r + 1) :=
  ⟨(Pi.single (Sum.inl 0) 1, Pi.single (Sum.inr 0) 1), by simp [pairing_neg_basis]⟩

theorem exists_hyperbolicPair_word (r : ℕ) (hr : 0 < r)
    (p : HyperbolicPairs K (r + 1)) :
    ∃ g : elementaryRootGroup K (r + 1), g • standardHyperbolicPair K r = p := by
  have hp : p.val.1 ≠ 0 := by
    intro hz
    have h := p.property
    rw [hz, pairing_zero_left] at h
    exact zero_ne_one h
  obtain ⟨a, ha⟩ := exists_elementary_mulVec_first_basis K r hr p.val.1 hp
  let e : Index (r + 1) → K := Pi.single (Sum.inl 0) 1
  let f : Index (r + 1) → K := Pi.single (Sum.inr 0) 1
  have hef : pairing (r + 1) e f = 1 := by simp [e, f, pairing_neg_basis]
  have hpaf : pairing (r + 1) p.val.1 ((a.val : Mat K (r + 1)) *ᵥ f) = 1 := by
    have h := elementary_preserves_pairing (r + 1) a e f
    rw [ha, hef] at h
    exact h
  obtain ⟨b, hbp, hbw⟩ := exists_elementary_fix_hyperbolic_partner r hr p.val.1 p.val.2
    ((a.val : Mat K (r + 1)) *ᵥ f) p.property hpaf
  refine ⟨b * a, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · change ((b.val : Mat K (r + 1)) * (a.val : Mat K (r + 1))) *ᵥ e = p.val.1
    rw [← Matrix.mulVec_mulVec, ha, hbp]
  · change ((b.val : Mat K (r + 1)) * (a.val : Mat K (r + 1))) *ᵥ f = p.val.2
    rw [← Matrix.mulVec_mulVec, hbw]

theorem standardHyperbolicPair_orbit (r : ℕ) (hr : 0 < r) :
    MulAction.orbit (elementaryRootGroup K (r + 1)) (standardHyperbolicPair K r) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  exact exists_hyperbolicPair_word K r hr p

def standardPairStabilizerEquiv (r : ℕ) :
    MulAction.stabilizer (elementaryRootGroup K (r + 1)) (standardHyperbolicPair K r) ≃
      firstPairElementary K r where
  toFun g := ⟨g.val.val, g.val.property, by
    have h : g.val • standardHyperbolicPair K r = standardHyperbolicPair K r := g.property
    exact ⟨congrArg (fun p : HyperbolicPairs K (r + 1) => p.val.1) h,
      congrArg (fun p : HyperbolicPairs K (r + 1) => p.val.2) h⟩⟩
  invFun c := ⟨⟨c.val, c.property.1⟩, by
    change (⟨c.val, c.property.1⟩ : elementaryRootGroup K (r + 1)) •
      standardHyperbolicPair K r = standardHyperbolicPair K r
    apply Subtype.ext
    exact Prod.ext c.property.2.1 c.property.2.2⟩
  left_inv g := by apply Subtype.ext; rfl
  right_inv c := by apply Subtype.ext; rfl

theorem elementary_card_hyperbolicPair_recurrence [Finite K] (r : ℕ) (hr : 0 < r) :
    Nat.card (elementaryRootGroup K (r + 1)) =
      Nat.card (HyperbolicPairs K (r + 1)) * Nat.card (elementaryRootGroup K r) := by
  have horbit : Nat.card (MulAction.orbit (elementaryRootGroup K (r + 1))
      (standardHyperbolicPair K r)) = Nat.card (HyperbolicPairs K (r + 1)) := by
    rw [standardHyperbolicPair_orbit K r hr]
    exact Nat.card_congr (Equiv.Set.univ _)
  have hstab : Nat.card (MulAction.stabilizer (elementaryRootGroup K (r + 1))
      (standardHyperbolicPair K r)) = Nat.card (elementaryRootGroup K r) :=
    (Nat.card_congr (standardPairStabilizerEquiv K r)).trans (firstPairElementary_card K r)
  have h := (Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup
    (elementaryRootGroup K (r + 1)) (standardHyperbolicPair K r))).symm
  rw [Nat.card_prod, horbit, hstab] at h
  exact h

end SymmetricSubgroupAsymptotics.CFSGSymplecticStabilizerCoordinates
