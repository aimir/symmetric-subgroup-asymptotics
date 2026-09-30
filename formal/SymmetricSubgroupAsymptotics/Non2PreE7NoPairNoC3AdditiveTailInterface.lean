import SymmetricSubgroupAsymptotics.Non2PreE7NoPairNoC3ConcreteInterface
import SymmetricSubgroupAsymptotics.GrowingQuotientAdditiveTail

/-!
# Additive-tail interface for the final pre-E7 residual

Historical owner bounds need not all be squeezed into one multiplicative
complete-quotient envelope.  This interface retains, on every literal normal
axis, a comparator-weighted main coefficient and a source-independent tail.
After summing the axes, only the main coefficient enters the quotient moment;
the tail is paid by a separate cold row.

The owner order is used only by the physical cover to select one orbit.  The
per-axis estimate below is unconditional on exclusion of earlier owners, so a
family certificate may be chosen independently for each retained action
class.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

open RepeatedMarkerOwnerBound

/-! ## Cover-parametric additive data

The historical first-owner interface selected an arbitrary violating orbit
after deciding the global owner.  Family certificates instead need a cover
which displays an orbit carrying the chosen certificate.  The following
version therefore takes the exact local predicate and its literal physical
cover as data.  It is the transfer target used by the certificate catalogue;
the older order-only wrapper below remains as a compatibility constructor. -/

structure PreE7NoPairNoC3LocalAdditiveAxisData (r : ℕ) where
  P : ∀ w (i : PreE7NonPairFirstOwnerIndex (r + 1) w) b,
    Subgroup (preE7NonPairFirstOwnerAction w i × Equiv.Perm (Fin b)) → Prop
  P_natural : ∀ w i b,
    FusionOrbitNatural (preE7NonPairFirstOwnerAction w i) (P w i b)
  physical_cover : ∀ n (H : Subgroup (Equiv.Perm (Fin n))),
    H ∈ PreE7NoPairNoC3ResidualSubgroupSet n →
      ∃ j : GrowingQuotientPhysicalIndex
          (ι := fun w => PreE7NonPairFirstOwnerIndex (r + 1) w) 3 n,
        H ∈ GrowingQuotientCanonicalFamily 3 n
          preE7NonPairFirstOwnerAction P j
  R : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → Type
  [groupR : ∀ w i, Group (R w i)]
  [finiteR : ∀ w i, Finite (R w i)]
  C : ∀ w (i : PreE7NonPairFirstOwnerIndex (r + 1) w) (_b : ℕ),
    {N : Subgroup (preE7NonPairFirstOwnerAction w i) // N.Normal} → ℝ
  tailCoefficient :
    ∀ w (i : PreE7NonPairFirstOwnerIndex (r + 1) w) (_b : ℕ),
      {N : Subgroup (preE7NonPairFirstOwnerAction w i) // N.Normal} → ℝ
  v : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → ℕ
  eta : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → ℝ
  delta : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → ℝ
  cutoff : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → ℝ
  alpha : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → ℝ
  theta : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → ℝ
  action : ∀ w i, R w i →* Equiv.Perm (Fin (v w i))
  action_injective : ∀ w i, Function.Injective (action w i)
  coefficient_nonneg : ∀ w i b N, 0 ≤ C w i b N
  tail_nonneg : ∀ w i b N, 0 ≤ tailCoefficient w i b N
  alpha_eq : ∀ w i, alpha w i = eta w i + cutoff w i
  axis_envelope : ∀ w i b N
      (J : Subgroup (Equiv.Perm (Fin b))),
    fusionSurvivingEpiCount (preE7NonPairFirstOwnerAction w i)
        (P w i b) N J ≤
      (C w i b N * (2 : ℝ) ^ (eta w i * b)) *
          completeQuotientWeight (R := R w i) J +
        tailCoefficient w i b N * (2 : ℝ) ^ (theta w i * b)

attribute [instance]
  PreE7NoPairNoC3LocalAdditiveAxisData.groupR
  PreE7NoPairNoC3LocalAdditiveAxisData.finiteR

def PreE7NoPairNoC3LocalAdditiveAxisData.mainTotal {r : ℕ}
    (D : PreE7NoPairNoC3LocalAdditiveAxisData r)
    (w : ℕ) (i : PreE7NonPairFirstOwnerIndex (r + 1) w) (b : ℕ) : ℝ :=
  fusionAxisEnvelopeTotal (preE7NonPairFirstOwnerAction w i) (D.C w i b)

def PreE7NoPairNoC3LocalAdditiveAxisData.tailTotal {r : ℕ}
    (D : PreE7NoPairNoC3LocalAdditiveAxisData r)
    (w : ℕ) (i : PreE7NonPairFirstOwnerIndex (r + 1) w) (b : ℕ) : ℝ :=
  fusionAxisEnvelopeTotal
    (preE7NonPairFirstOwnerAction w i) (D.tailCoefficient w i b)

def PreE7NoPairNoC3LocalAdditiveAxisData.normalizer {r : ℕ}
    (_D : PreE7NoPairNoC3LocalAdditiveAxisData r)
    (w : ℕ) (i : PreE7NonPairFirstOwnerIndex (r + 1) w) : ℝ :=
  Nat.card (Subgroup.normalizer
    (preE7NonPairFirstOwnerAction w i : Set (Equiv.Perm (Fin w))))

theorem PreE7NoPairNoC3LocalAdditiveAxisData.mainTotal_nonneg {r : ℕ}
    (D : PreE7NoPairNoC3LocalAdditiveAxisData r) (w i b) :
    0 ≤ D.mainTotal w i b :=
  fusionAxisEnvelopeTotal_nonneg _ _ (D.coefficient_nonneg w i b)

theorem PreE7NoPairNoC3LocalAdditiveAxisData.tailTotal_nonneg {r : ℕ}
    (D : PreE7NoPairNoC3LocalAdditiveAxisData r) (w i b) :
    0 ≤ D.tailTotal w i b :=
  fusionAxisEnvelopeTotal_nonneg _ _ (D.tail_nonneg w i b)

theorem PreE7NoPairNoC3LocalAdditiveAxisData.completeSource_envelope
    {r : ℕ} (D : PreE7NoPairNoC3LocalAdditiveAxisData r)
    (w : ℕ) (i : PreE7NonPairFirstOwnerIndex (r + 1) w) (b : ℕ)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionCompleteSourceSum (preE7NonPairFirstOwnerAction w i)
        (D.P w i b) J ≤
      (D.mainTotal w i b * (2 : ℝ) ^ (D.eta w i * b)) *
          completeQuotientWeight (R := D.R w i) J +
        D.tailTotal w i b * (2 : ℝ) ^ (D.theta w i * b) := by
  unfold fusionCompleteSourceSum mainTotal tailTotal fusionAxisEnvelopeTotal
  calc
    _ ≤ ∑ N, ((D.C w i b N * (2 : ℝ) ^ (D.eta w i * b)) *
          completeQuotientWeight (R := D.R w i) J +
        D.tailCoefficient w i b N * (2 : ℝ) ^ (D.theta w i * b)) :=
      Finset.sum_le_sum (fun N _ => D.axis_envelope w i b N J)
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_mul]

structure PreE7NoPairNoC3LocalAdditiveNumericalCertificate {r : ℕ}
    (D : PreE7NoPairNoC3LocalAdditiveAxisData r) where
  rho : ℝ
  rho_pos : 0 < rho
  rho_le_eighth : rho ≤ 1 / 8
  parameters : GrowingQuotientParameterBound rho
    D.v D.eta D.delta D.cutoff D.alpha
  tail_gap : ∀ w i,
    D.theta w i ≤ (halfDegree w : ℝ) / 4 - rho * w / 4
  main_menu : GrowingMenuMassBound 3 D.mainTotal D.normalizer
  tail_menu : GrowingMenuMassBound 3 D.tailTotal D.normalizer

/-- The additive transfer with a certificate-retaining physical cover. -/
noncomputable def
    preE7NoPairNoC3_exponentialForwardEstimate_of_localAdditiveAxisData
    {r : ℕ}
    (D : PreE7NoPairNoC3LocalAdditiveAxisData r)
    (Numerics : PreE7NoPairNoC3LocalAdditiveNumericalCertificate D)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ))) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      preE7NoPairNoC3ResidualRatio := by
  have hlocal : GrowingQuotientAdditiveTailLocalPhysicalBound 3
      preE7NonPairFirstOwnerAction D.P
      D.mainTotal D.tailTotal D.normalizer D.v D.eta D.delta D.cutoff
        D.alpha D.theta :=
    growingQuotientAdditiveTailLocalPhysicalBound_of_completeSource 3
      preE7NonPairFirstOwnerAction D.P
      D.R D.mainTotal D.tailTotal D.normalizer D.v D.eta D.delta
      D.cutoff D.alpha D.theta D.action D.action_injective D.P_natural
      D.mainTotal_nonneg D.tailTotal_nonneg (fun _ _ => rfl) D.alpha_eq
      D.completeSource_envelope
  have hphysical : GrowingQuotientAdditiveTailPhysicalBound
      preE7NoPairNoC3ResidualRatio 3 D.mainTotal D.tailTotal
      D.normalizer D.v D.eta D.delta D.cutoff D.alpha D.theta :=
    growingQuotientAdditiveTailPhysicalBound_of_local
      preE7NoPairNoC3ResidualRatio 3 (by omega)
      PreE7NoPairNoC3ResidualSubgroupSet preE7NonPairFirstOwnerAction D.P
      D.mainTotal D.tailTotal D.normalizer D.v D.eta D.delta D.cutoff
      D.alpha D.theta
      (Filter.Eventually.of_forall (fun n => by
        rw [preE7NoPairNoC3ResidualRatio_eq_subgroupSet n]))
      D.physical_cover hlocal
  exact growingQuotientAdditiveTail_exponentialForwardEstimate
    preE7NoPairNoC3ResidualRatio 3 D.mainTotal D.tailTotal D.normalizer
    D.v D.eta D.delta D.cutoff D.alpha D.theta Numerics.rho_pos
    Numerics.rho_le_eighth (by omega) D.mainTotal_nonneg
    D.tailTotal_nonneg
    (fun w i => by
      unfold PreE7NoPairNoC3LocalAdditiveAxisData.normalizer
      exact_mod_cast (Nat.card_pos (α := Subgroup.normalizer
        (preE7NonPairFirstOwnerAction w i :
          Set (Equiv.Perm (Fin w))))))
    Numerics.parameters Numerics.tail_gap Numerics.main_menu
    Numerics.tail_menu hcoarse hphysical

/-- A combined per-axis envelope.  `C` is the comparator-weighted part and
`Tail` is the pure cold part.  Both are charged before the original action's
normalizer division. -/
structure PreE7NoPairNoC3AdditiveAxisData (r : ℕ) where
  Earlier : ∀ d, Fin r → Subgroup (Equiv.Perm (Fin d)) → Prop
  earlier_natural : DegreeNaturalOwnerMenu Earlier
  R : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → Type
  [groupR : ∀ w i, Group (R w i)]
  [finiteR : ∀ w i, Finite (R w i)]
  C : ∀ w (i : PreE7NonPairFirstOwnerIndex (r + 1) w) (_b : ℕ),
    {N : Subgroup (preE7NonPairFirstOwnerAction w i) // N.Normal} → ℝ
  tailCoefficient :
    ∀ w (i : PreE7NonPairFirstOwnerIndex (r + 1) w) (_b : ℕ),
      {N : Subgroup (preE7NonPairFirstOwnerAction w i) // N.Normal} → ℝ
  v : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → ℕ
  eta : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → ℝ
  delta : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → ℝ
  cutoff : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → ℝ
  alpha : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → ℝ
  theta : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → ℝ
  action : ∀ w i, R w i →* Equiv.Perm (Fin (v w i))
  action_injective : ∀ w i, Function.Injective (action w i)
  coefficient_nonneg : ∀ w i b N, 0 ≤ C w i b N
  tail_nonneg : ∀ w i b N, 0 ≤ tailCoefficient w i b N
  alpha_eq : ∀ w i, alpha w i = eta w i + cutoff w i
  axis_envelope : ∀ w i b N
      (J : Subgroup (Equiv.Perm (Fin b))),
    fusionSurvivingEpiCount (preE7NonPairFirstOwnerAction w i)
        (preE7NoPairNoC3FirstOwnerPredicate
          (ownerOrResidualEligible Earlier) w i b) N J ≤
      (C w i b N * (2 : ℝ) ^ (eta w i * b)) *
          completeQuotientWeight (R := R w i) J +
        tailCoefficient w i b N * (2 : ℝ) ^ (theta w i * b)

attribute [instance]
  PreE7NoPairNoC3AdditiveAxisData.groupR
  PreE7NoPairNoC3AdditiveAxisData.finiteR

/-- Literal sum of the comparator coefficients over all normal axes. -/
def PreE7NoPairNoC3AdditiveAxisData.mainTotal {r : ℕ}
    (D : PreE7NoPairNoC3AdditiveAxisData r)
    (w : ℕ) (i : PreE7NonPairFirstOwnerIndex (r + 1) w) (b : ℕ) : ℝ :=
  fusionAxisEnvelopeTotal (preE7NonPairFirstOwnerAction w i) (D.C w i b)

/-- Literal sum of the additive coefficients over all normal axes. -/
def PreE7NoPairNoC3AdditiveAxisData.tailTotal {r : ℕ}
    (D : PreE7NoPairNoC3AdditiveAxisData r)
    (w : ℕ) (i : PreE7NonPairFirstOwnerIndex (r + 1) w) (b : ℕ) : ℝ :=
  fusionAxisEnvelopeTotal
    (preE7NonPairFirstOwnerAction w i) (D.tailCoefficient w i b)

/-- The original action normalizer retained by the physical count. -/
def PreE7NoPairNoC3AdditiveAxisData.normalizer {r : ℕ}
    (_D : PreE7NoPairNoC3AdditiveAxisData r)
    (w : ℕ) (i : PreE7NonPairFirstOwnerIndex (r + 1) w) : ℝ :=
  Nat.card (Subgroup.normalizer
    (preE7NonPairFirstOwnerAction w i : Set (Equiv.Perm (Fin w))))

theorem PreE7NoPairNoC3AdditiveAxisData.mainTotal_nonneg {r : ℕ}
    (D : PreE7NoPairNoC3AdditiveAxisData r) (w i b) :
    0 ≤ D.mainTotal w i b :=
  fusionAxisEnvelopeTotal_nonneg _ _ (D.coefficient_nonneg w i b)

theorem PreE7NoPairNoC3AdditiveAxisData.tailTotal_nonneg {r : ℕ}
    (D : PreE7NoPairNoC3AdditiveAxisData r) (w i b) :
    0 ≤ D.tailTotal w i b :=
  fusionAxisEnvelopeTotal_nonneg _ _ (D.tail_nonneg w i b)

theorem PreE7NoPairNoC3AdditiveAxisData.completeSource_envelope
    {r : ℕ} (D : PreE7NoPairNoC3AdditiveAxisData r)
    (w : ℕ) (i : PreE7NonPairFirstOwnerIndex (r + 1) w) (b : ℕ)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionCompleteSourceSum (preE7NonPairFirstOwnerAction w i)
        (preE7NoPairNoC3FirstOwnerPredicate
          (ownerOrResidualEligible D.Earlier) w i b) J ≤
      (D.mainTotal w i b * (2 : ℝ) ^ (D.eta w i * b)) *
          completeQuotientWeight (R := D.R w i) J +
        D.tailTotal w i b * (2 : ℝ) ^ (D.theta w i * b) := by
  unfold fusionCompleteSourceSum mainTotal tailTotal fusionAxisEnvelopeTotal
  calc
    _ ≤ ∑ N, ((D.C w i b N * (2 : ℝ) ^ (D.eta w i * b)) *
          completeQuotientWeight (R := D.R w i) J +
        D.tailCoefficient w i b N * (2 : ℝ) ^ (D.theta w i * b)) :=
      Finset.sum_le_sum (fun N _ => D.axis_envelope w i b N J)
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_mul]

/-- Numerical hypotheses for both coefficient menus.  The main menu obeys
the usual growing-comparator parameters; the tail exponent has a direct cold
gap. -/
structure PreE7NoPairNoC3AdditiveNumericalCertificate {r : ℕ}
    (D : PreE7NoPairNoC3AdditiveAxisData r) where
  rho : ℝ
  rho_pos : 0 < rho
  rho_le_eighth : rho ≤ 1 / 8
  parameters : GrowingQuotientParameterBound rho
    D.v D.eta D.delta D.cutoff D.alpha
  tail_gap : ∀ w i,
    D.theta w i ≤ (halfDegree w : ℝ) / 4 - rho * w / 4
  main_menu : GrowingMenuMassBound 3 D.mainTotal D.normalizer
  tail_menu : GrowingMenuMassBound 3 D.tailTotal D.normalizer

/-- The combined additive per-axis data close the exact no-pair/no-`C3`
physical residual. -/
noncomputable def preE7NoPairNoC3_exponentialForwardEstimate_of_additiveAxisData
    {r : ℕ}
    (D : PreE7NoPairNoC3AdditiveAxisData r)
    (Numerics : PreE7NoPairNoC3AdditiveNumericalCertificate D)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ))) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      preE7NoPairNoC3ResidualRatio := by
  have hP : ∀ w i b, FusionOrbitNatural
      (preE7NonPairFirstOwnerAction w i)
      (preE7NoPairNoC3FirstOwnerPredicate
        (ownerOrResidualEligible D.Earlier) w i b) := by
    intro w i b
    exact preE7NoPairNoC3FirstOwnerPredicate_natural
      (ownerOrResidualEligible D.Earlier)
      (ownerOrResidualEligible_natural D.Earlier D.earlier_natural) w i b
  have hlocal : GrowingQuotientAdditiveTailLocalPhysicalBound 3
      preE7NonPairFirstOwnerAction
      (preE7NoPairNoC3FirstOwnerPredicate
        (ownerOrResidualEligible D.Earlier))
      D.mainTotal D.tailTotal D.normalizer D.v D.eta D.delta D.cutoff
        D.alpha D.theta :=
    growingQuotientAdditiveTailLocalPhysicalBound_of_completeSource 3
      preE7NonPairFirstOwnerAction
      (preE7NoPairNoC3FirstOwnerPredicate
        (ownerOrResidualEligible D.Earlier))
      D.R D.mainTotal D.tailTotal D.normalizer D.v D.eta D.delta
      D.cutoff D.alpha D.theta D.action D.action_injective hP
      D.mainTotal_nonneg D.tailTotal_nonneg (fun _ _ => rfl) D.alpha_eq
      D.completeSource_envelope
  have hphysical : GrowingQuotientAdditiveTailPhysicalBound
      preE7NoPairNoC3ResidualRatio 3 D.mainTotal D.tailTotal
      D.normalizer D.v D.eta D.delta D.cutoff D.alpha D.theta :=
    growingQuotientAdditiveTailPhysicalBound_of_local
      preE7NoPairNoC3ResidualRatio 3 (by omega)
      PreE7NoPairNoC3ResidualSubgroupSet preE7NonPairFirstOwnerAction
      (preE7NoPairNoC3FirstOwnerPredicate
        (ownerOrResidualEligible D.Earlier))
      D.mainTotal D.tailTotal D.normalizer D.v D.eta D.delta D.cutoff
      D.alpha D.theta
      (Filter.Eventually.of_forall (fun n => by
        rw [preE7NoPairNoC3ResidualRatio_eq_subgroupSet n]))
      (preE7NoPairNoC3_ownerOrResidual_physical_cover
        D.Earlier D.earlier_natural) hlocal
  exact growingQuotientAdditiveTail_exponentialForwardEstimate
    preE7NoPairNoC3ResidualRatio 3 D.mainTotal D.tailTotal D.normalizer
    D.v D.eta D.delta D.cutoff D.alpha D.theta Numerics.rho_pos
    Numerics.rho_le_eighth (by omega) D.mainTotal_nonneg
    D.tailTotal_nonneg
    (fun w i => by
      unfold PreE7NoPairNoC3AdditiveAxisData.normalizer
      exact_mod_cast (Nat.card_pos (α := Subgroup.normalizer
        (preE7NonPairFirstOwnerAction w i :
          Set (Equiv.Perm (Fin w))))))
    Numerics.parameters Numerics.tail_gap Numerics.main_menu
    Numerics.tail_menu hcoarse hphysical

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
