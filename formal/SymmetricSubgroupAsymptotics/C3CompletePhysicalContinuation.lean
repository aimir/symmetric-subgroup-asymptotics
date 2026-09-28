import SymmetricSubgroupAsymptotics.C3PhysicalOwnerFiniteContinuation
import SymmetricSubgroupAsymptotics.C3ResidualForwardEstimate

/-!
# Complete continuation for the regular-C3 audit

The noncritical regular-C3 family is split on the complete physical subgroup.
If the invariant high-C3 structural owner accepts it, it enters the finite
first-owner continuation. Otherwise every earlier structural branch rejects
it, so the same local chart belongs to the already closed final residual row.
The two exponential forward estimates therefore assemble without losing the
original action weight or changing the literal complement degree.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- The complete ordinary filter in the fixed regular-C3 chart. -/
def C3CompleteOrdinaryPredicate (b : ℕ)
    (H : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b))) : Prop :=
  ¬ IsCriticalSubgroup (3+b)
      (relabelSubgroup (c3ResidualPointEquiv b)
        (H.map (fusionOrbitAction ternaryRegularAction)))

theorem c3CompleteOrdinaryPredicate_natural (b : ℕ) :
    FusionOrbitNatural ternaryRegularAction
      (C3CompleteOrdinaryPredicate b) := by
  apply fusionOrbitNatural_of_relabel_invariant ternaryRegularAction
    (c3ResidualPointEquiv b)
    (fun G => ¬ IsCriticalSubgroup (3+b) G)
  intro s G
  exact ordinaryRemainder_relabel_iff (3+b) s G

/-- Put the complete labelled regular-C3 family on the fixed physical labels
used by its structural owner and residual predicates. -/
def C3CompleteOrdinaryPhysicalSet (b : ℕ) :
    Set (Subgroup (Equiv.Perm (Fin (3+b)))) :=
  FusionRelabelledFamily (c3ResidualPointEquiv b)
    (FusionOrbitFamily ternaryRegularAction
      (FusionAcceptedOrbitPredicate ternaryRegularAction
        (C3CompleteOrdinaryPredicate b)))

/-- The final residual family on the same complete physical labels. -/
def C3FinalResidualPhysicalSet (b : ℕ) :
    Set (Subgroup (Equiv.Perm (Fin (3+b)))) :=
  FusionRelabelledFamily (c3ResidualPointEquiv b)
    (FusionOrbitFamily ternaryRegularAction
      (FusionAcceptedOrbitPredicate ternaryRegularAction
        (C3FinalResidualPredicate b)))

/-- Every complete noncritical regular-C3 subgroup is accepted by the
invariant structural owner or by the appended residual owner. The split is
performed after all physical relabellings, so it does not depend on a chosen
local chart. -/
theorem c3CompleteOrdinaryPhysical_owner_or_residual
    (b : ℕ) (G : Subgroup (Equiv.Perm (Fin (3+b))))
    (hG : G ∈ C3CompleteOrdinaryPhysicalSet b) :
    G ∈ C3PhysicalStructuralOwnerSet (3+b) ∨
      G ∈ C3FinalResidualPhysicalSet b := by
  obtain ⟨⟨K, hK⟩, rfl⟩ := hG
  obtain ⟨⟨s, ⟨M, hM⟩⟩, rfl⟩ := hK
  obtain ⟨H, hAccepted, rfl⟩ := hM
  let K₀ := H.1.map (fusionOrbitAction ternaryRegularAction)
  let t : Equiv.Perm (Fin (3+b)) :=
    (c3ResidualPointEquiv b).symm.trans
      (s.trans (c3ResidualPointEquiv b))
  have ht : (c3ResidualPointEquiv b).trans t =
      s.trans (c3ResidualPointEquiv b) := by
    ext x
    simp only [t, Equiv.trans_apply, Equiv.symm_apply_apply]
  have hphysical :
      relabelSubgroup (c3ResidualPointEquiv b)
          (relabelSubgroup s K₀) =
        relabelSubgroup t
          (relabelSubgroup (c3ResidualPointEquiv b) K₀) := by
    simp only [relabelSubgroup_trans, ht]
  have hnoncritical₀ :
      ¬ IsCriticalSubgroup (3+b)
        (relabelSubgroup (c3ResidualPointEquiv b) K₀) := H.2.2
  have hnoncritical :
      ¬ IsCriticalSubgroup (3+b)
        (relabelSubgroup (c3ResidualPointEquiv b)
          (relabelSubgroup s K₀)) := by
    rw [hphysical]
    exact (ordinaryRemainder_relabel_iff (3+b) t _).mpr hnoncritical₀
  by_cases hOwner : C3PhysicalStructuralOwner (3+b)
      (relabelSubgroup (c3ResidualPointEquiv b)
        (relabelSubgroup s K₀))
  · exact Or.inl ⟨hnoncritical, hOwner⟩
  · right
    have hOwner₀ : ¬ C3PhysicalStructuralOwner (3+b)
        (relabelSubgroup (c3ResidualPointEquiv b) K₀) := by
      intro h
      apply hOwner
      rw [hphysical]
      exact (c3PhysicalStructuralOwner_relabel_iff rfl t _).mpr h
    have hRejects : ∀ i : Fin 4,
        ¬ c3PhysicalStructuralBranchMenu (3+b) i
          (relabelSubgroup (c3ResidualPointEquiv b) K₀) := by
      intro i hi
      apply hOwner₀
      exact c3PhysicalStructuralOwnerBranch_owner hi
    have hResidual : C3FinalResidualPredicate b H.1 := by
      refine ⟨hnoncritical₀, ?_⟩
      exact (firstOwned_ownerOrResidual_last_iff
        c3PhysicalStructuralBranchMenu _).mpr hRejects
    refine ⟨⟨relabelSubgroup s K₀, ?_⟩, rfl⟩
    refine ⟨⟨s, ⟨K₀, ?_⟩⟩, rfl⟩
    exact ⟨⟨H.1, ⟨H.2.1, hResidual⟩⟩, rfl⟩

def c3CompletePhysicalBranchFamily (b : ℕ) :
    Fin 2 → Set (Subgroup (Equiv.Perm (Fin (3+b))))
  | 0 => C3PhysicalStructuralOwnerSet (3+b)
  | 1 => C3FinalResidualPhysicalSet b

theorem c3CompleteOrdinaryPhysical_card_le (b : ℕ) :
    Nat.card (C3CompleteOrdinaryPhysicalSet b) ≤
      Nat.card (C3PhysicalStructuralOwnerSet (3+b)) +
        Nat.card (C3FinalResidualPhysicalSet b) := by
  have h := fusionPhysicalUnion_card_le
    (C3CompleteOrdinaryPhysicalSet b)
    (c3CompletePhysicalBranchFamily b)
    (fun G hG => by
      rcases c3CompleteOrdinaryPhysical_owner_or_residual b G hG with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩)
  simpa only [Fin.sum_univ_two, c3CompletePhysicalBranchFamily] using h

/-- The normalized complete noncritical regular-C3 family at ambient degree
`n`, with its literal three-point orbit removed. -/
def c3CompleteOrdinaryRatio (n : ℕ) : ℝ :=
  if 3 ≤ n then
    (Nat.card (C3CompleteOrdinaryPhysicalSet (n-3)) : ℝ) /
      exactBenchmark n
  else 0

theorem c3CompleteOrdinaryRatio_le_owner_add_residual
    (n : ℕ) (hn : 3 ≤ n) :
    c3CompleteOrdinaryRatio n ≤
      c3PhysicalStructuralOwnerRatio n + c3FinalResidualRatio n := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hsub : 3 + b - 3 = b := by omega
  have hcard := c3CompleteOrdinaryPhysical_card_le b
  have hcardR :
      (Nat.card (C3CompleteOrdinaryPhysicalSet b) : ℝ) ≤
        (Nat.card (C3PhysicalStructuralOwnerSet (3+b)) : ℝ) +
          (Nat.card (C3FinalResidualPhysicalSet b) : ℝ) := by
    exact_mod_cast hcard
  have hrescard :
      Nat.card (C3FinalResidualPhysicalSet b) =
        Nat.card (FusionOrbitFamily ternaryRegularAction
          (FusionAcceptedOrbitPredicate ternaryRegularAction
            (C3FinalResidualPredicate b))) := by
    unfold C3FinalResidualPhysicalSet
    exact fusionRelabelledFamily_card _ _
  rw [hrescard] at hcardR
  unfold c3CompleteOrdinaryRatio c3PhysicalStructuralOwnerRatio
    c3FinalResidualRatio
  rw [if_pos (by omega), if_pos (by omega), hsub]
  exact (div_le_div_of_nonneg_right hcardR
    (exactBenchmark_pos (3+b)).le).trans_eq (by ring)

/-- The finite high-owner rows and the closed residual row form one complete
exponential forward estimate for the regular-C3 ordinary audit. -/
noncomputable def c3CompleteOrdinary_exponentialForwardEstimate
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (f : C3HighFirstOwnerIndex → ℕ → ℝ)
    (hf : ∀ j b, 0 ≤ f j b)
    (hdecay : ∀ j, ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧
      ∀ᶠ b : ℕ in atTop, f j b ≤ C * (2 : ℝ) ^ (-κ * (b : ℝ)))
    (hlocal : ∀ (j : C3HighFirstOwnerIndex) (n : ℕ)
      (hn : c3HighFirstOwnerWidth j ≤ n),
      (Nat.card (FusionWidthCanonicalFamily
        (c3HighFirstOwnerAction j) hn
        (c3HighFirstOwnerPredicate j
          (n - c3HighFirstOwnerWidth j))) : ℝ) /
          exactBenchmark n ≤
        f j (n - c3HighFirstOwnerWidth j) *
          ordinarySubgroupRatio (n - c3HighFirstOwnerWidth j)) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      c3CompleteOrdinaryRatio := by
  let Eowner := c3PhysicalStructuralOwner_exponentialForwardEstimate
    hChief hWeight hPrimitive h18 f hf hdecay hlocal
  let Eresidual := c3FinalResidual_exponentialForwardEstimate
    hChief hWeight hPrimitive h18
  exact OrdinaryFrontierClosure.ExponentialForwardEstimate.of_le
    (OrdinaryFrontierClosure.ExponentialForwardEstimate.add Eowner Eresidual)
    3 c3CompleteOrdinaryRatio_le_owner_add_residual

end SymmetricSubgroupAsymptotics

end
