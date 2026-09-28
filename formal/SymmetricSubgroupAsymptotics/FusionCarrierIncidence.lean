import SymmetricSubgroupAsymptotics.FusionCarrierOwnerCapacity

/-!
# Direct incidence bounds for reversible fusion carriers

An accepted intrinsic carrier epimorphism may be sent to a complete quotient
map with the same literal exterior source.  A uniform bound on the fibres of
that map is therefore exactly an owner-capacity estimate.  The second form
retains an additional finite flag in every cell; this is the interface for
radical flags and restricted transgression-annihilator data.  Such flags are
counted before the complete quotient moment is invoked, rather than being
discarded in a structural classification.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

attribute [local instance] Fintype.ofFinite

/-- A uniform fibre bound for a map between finite types.  This is stated
with `Nat.card`, so applications do not have to install chosen enumerations
of their intrinsic carrier families. -/
theorem natCard_le_uniformFiber_mul
    {X Y : Type*} [Finite X] [Finite Y]
    (f : X → Y) (L : ℕ)
    (hfibre : ∀ y : Y, Nat.card {x : X // f x = y} ≤ L) :
    Nat.card X ≤ L * Nat.card Y := by
  calc
    Nat.card X = Nat.card (Σ y : Y, {x : X // f x = y}) :=
      (Nat.card_congr (Equiv.sigmaFiberEquiv f)).symm
    _ = ∑ y : Y, Nat.card {x : X // f x = y} := Nat.card_sigma
    _ ≤ ∑ _y : Y, L := Finset.sum_le_sum (fun y _ ↦ hfibre y)
    _ = L * Nat.card Y := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_eq_nat_card]
      exact Nat.mul_comm _ _

/-- The accepted epimorphisms on one intrinsic carrier axis. -/
abbrev FusionCarrierAcceptedEpi
    {w q b : ℕ}
    (C : CheckedPermutationCarrier w q)
    (J : Subgroup (Equiv.Perm (Fin b)))
    (Accepted : Subgroup (C.carrier × Equiv.Perm (Fin b)) → Prop) :=
  {δ : GroupEpimorphism J C.quotient //
    Accepted (fusionQuotientGraph C.beta J δ.1)}

/-- A direct `(K,f)` incidence: each accepted carrier epimorphism has one
complete comparator map, and each comparator fibre has capacity at most
`L`.  The conclusion is the exact real-valued envelope used by fusion. -/
theorem fusionCarrierAcceptedEpi_card_le_of_incidence
    {w q b : ℕ}
    (C : CheckedPermutationCarrier w q)
    (J : Subgroup (Equiv.Perm (Fin b)))
    (Accepted : Subgroup (C.carrier × Equiv.Perm (Fin b)) → Prop)
    {R : Type*} [Group R] [Finite R]
    (f : FusionCarrierAcceptedEpi C J Accepted → CompleteQuotientMap J R)
    (L : ℕ)
    (hfibre : ∀ d : CompleteQuotientMap J R,
      Nat.card {δ : FusionCarrierAcceptedEpi C J Accepted // f δ = d} ≤ L) :
    (Nat.card (FusionCarrierAcceptedEpi C J Accepted) : ℝ) ≤
      (L : ℝ) * completeQuotientWeight (R := R) J := by
  have hnat := natCard_le_uniformFiber_mul f L hfibre
  rw [completeQuotientMap_card] at hnat
  unfold completeQuotientWeight
  exact_mod_cast hnat

/-- Numerical capacity version of the direct incidence theorem.  All
source-dependent growth is isolated in the uniform fibre capacity `L`. -/
theorem fusionCarrierAcceptedEpi_card_le_ownerCapacity_of_incidence
    {w q b : ℕ}
    (C : CheckedPermutationCarrier w q)
    (J : Subgroup (Equiv.Perm (Fin b)))
    (Accepted : Subgroup (C.carrier × Equiv.Perm (Fin b)) → Prop)
    {R : Type*} [Group R] [Finite R]
    (f : FusionCarrierAcceptedEpi C J Accepted → CompleteQuotientMap J R)
    (L : ℕ)
    (hfibre : ∀ d : CompleteQuotientMap J R,
      Nat.card {δ : FusionCarrierAcceptedEpi C J Accepted // f δ = d} ≤ L)
    (D eta : ℝ)
    (hcapacity : (L : ℝ) ≤ D * (2 : ℝ) ^ (eta * b)) :
    (Nat.card (FusionCarrierAcceptedEpi C J Accepted) : ℝ) ≤
      (D * (2 : ℝ) ^ (eta * b)) *
        completeQuotientWeight (R := R) J := by
  exact (fusionCarrierAcceptedEpi_card_le_of_incidence
    C J Accepted f L hfibre).trans
      (mul_le_mul_of_nonneg_right hcapacity
        (completeQuotientWeight_nonneg (R := R) J))

/-- Retained-cell incidence.  The map to `CompleteQuotientMap J R × A`
keeps a finite invariant flag `A` in the cell label.  Thus a radical flag or
restricted annihilator is not forgotten: its number of possible values is
charged explicitly, while `Z` bounds the remaining Yoneda fibre. -/
theorem fusionCarrierAcceptedEpi_card_le_of_retainedCells
    {w q b : ℕ}
    (C : CheckedPermutationCarrier w q)
    (J : Subgroup (Equiv.Perm (Fin b)))
    (Accepted : Subgroup (C.carrier × Equiv.Perm (Fin b)) → Prop)
    {R A : Type*} [Group R] [Finite R] [Finite A]
    (cell : FusionCarrierAcceptedEpi C J Accepted →
      CompleteQuotientMap J R × A)
    (Z : ℕ)
    (hcell : ∀ d : CompleteQuotientMap J R × A,
      Nat.card {δ : FusionCarrierAcceptedEpi C J Accepted // cell δ = d} ≤ Z) :
    (Nat.card (FusionCarrierAcceptedEpi C J Accepted) : ℝ) ≤
      (Nat.card A * Z : ℕ) * completeQuotientWeight (R := R) J := by
  have hnat := natCard_le_uniformFiber_mul cell Z hcell
  rw [Nat.card_prod, completeQuotientMap_card] at hnat
  have hreal :
      (Nat.card (FusionCarrierAcceptedEpi C J Accepted) : ℝ) ≤
        (Z * (completeQuotientCount (R := R) J * Nat.card A) : ℕ) := by
    exact_mod_cast hnat
  simpa only [completeQuotientWeight, Nat.cast_mul, mul_assoc, mul_comm,
    mul_left_comm] using hreal

/-- Numerical owner-capacity form of retained-cell incidence.  The entire
flag count and residual Yoneda fibre must fit under the stated quadratic
capacity; no unmarked residual estimate is accepted by this interface. -/
theorem fusionCarrierAcceptedEpi_card_le_ownerCapacity_of_retainedCells
    {w q b : ℕ}
    (C : CheckedPermutationCarrier w q)
    (J : Subgroup (Equiv.Perm (Fin b)))
    (Accepted : Subgroup (C.carrier × Equiv.Perm (Fin b)) → Prop)
    {R A : Type*} [Group R] [Finite R] [Finite A]
    (cell : FusionCarrierAcceptedEpi C J Accepted →
      CompleteQuotientMap J R × A)
    (Z : ℕ)
    (hcell : ∀ d : CompleteQuotientMap J R × A,
      Nat.card {δ : FusionCarrierAcceptedEpi C J Accepted // cell δ = d} ≤ Z)
    (D eta : ℝ)
    (hcapacity : (Nat.card A * Z : ℕ) ≤
      D * (2 : ℝ) ^ (eta * b)) :
    (Nat.card (FusionCarrierAcceptedEpi C J Accepted) : ℝ) ≤
      (D * (2 : ℝ) ^ (eta * b)) *
        completeQuotientWeight (R := R) J := by
  exact (fusionCarrierAcceptedEpi_card_le_of_retainedCells
    C J Accepted cell Z hcell).trans
      (mul_le_mul_of_nonneg_right hcapacity
        (completeQuotientWeight_nonneg (R := R) J))

namespace FusionAxisCarrier

/-- A direct comparator incidence on the intrinsic carrier discharges the
original surviving-epimorphism capacity on the exact literal axis. -/
theorem survivingEpiCount_le_of_incidence
    {w b : ℕ}
    {U : Subgroup (Equiv.Perm (Fin w))}
    {P : Subgroup (U × Equiv.Perm (Fin b)) → Prop}
    {N : {N : Subgroup U // N.Normal}}
    (K : FusionAxisCarrier U N)
    (J : Subgroup (Equiv.Perm (Fin b)))
    (Accepted : Subgroup (K.checked.carrier × Equiv.Perm (Fin b)) → Prop)
    (haccept : ∀ δ : GroupEpimorphism J K.checked.quotient,
      K.checked.carrierInverseSurvival K.source_eq P
          (fusionQuotientGraph K.checked.beta J δ.1) →
        Accepted (fusionQuotientGraph K.checked.beta J δ.1))
    {R : Type*} [Group R] [Finite R]
    (f : FusionCarrierAcceptedEpi K.checked J Accepted →
      CompleteQuotientMap J R)
    (L : ℕ)
    (hfibre : ∀ d : CompleteQuotientMap J R,
      Nat.card {δ : FusionCarrierAcceptedEpi K.checked J Accepted //
        f δ = d} ≤ L)
    (D eta : ℝ)
    (hcapacity : (L : ℝ) ≤ D * (2 : ℝ) ^ (eta * b)) :
    fusionSurvivingEpiCount U P N J ≤
      (D * (2 : ℝ) ^ (eta * b)) *
        completeQuotientWeight (R := R) J := by
  apply K.survivingEpiCount_le_of_intrinsic J Accepted haccept
  exact fusionCarrierAcceptedEpi_card_le_ownerCapacity_of_incidence
    K.checked J Accepted f L hfibre D eta hcapacity

/-- The annihilator-aware retained-cell theorem transported all the way
back to the original action.  Reversibility preserves the source `J`, the
literal normal axis, and every earlier-owner exclusion. -/
theorem survivingEpiCount_le_of_retainedCells
    {w b : ℕ}
    {U : Subgroup (Equiv.Perm (Fin w))}
    {P : Subgroup (U × Equiv.Perm (Fin b)) → Prop}
    {N : {N : Subgroup U // N.Normal}}
    (K : FusionAxisCarrier U N)
    (J : Subgroup (Equiv.Perm (Fin b)))
    (Accepted : Subgroup (K.checked.carrier × Equiv.Perm (Fin b)) → Prop)
    (haccept : ∀ δ : GroupEpimorphism J K.checked.quotient,
      K.checked.carrierInverseSurvival K.source_eq P
          (fusionQuotientGraph K.checked.beta J δ.1) →
        Accepted (fusionQuotientGraph K.checked.beta J δ.1))
    {R A : Type*} [Group R] [Finite R] [Finite A]
    (cell : FusionCarrierAcceptedEpi K.checked J Accepted →
      CompleteQuotientMap J R × A)
    (Z : ℕ)
    (hcell : ∀ d : CompleteQuotientMap J R × A,
      Nat.card {δ : FusionCarrierAcceptedEpi K.checked J Accepted //
        cell δ = d} ≤ Z)
    (D eta : ℝ)
    (hcapacity : (Nat.card A * Z : ℕ) ≤
      D * (2 : ℝ) ^ (eta * b)) :
    fusionSurvivingEpiCount U P N J ≤
      (D * (2 : ℝ) ^ (eta * b)) *
        completeQuotientWeight (R := R) J := by
  apply K.survivingEpiCount_le_of_intrinsic J Accepted haccept
  exact fusionCarrierAcceptedEpi_card_le_ownerCapacity_of_retainedCells
    K.checked J Accepted cell Z hcell D eta hcapacity

end FusionAxisCarrier

namespace RepeatedMarkerOwnerBound

/-- Full general non-2 forward estimate from earlier quotient owners and
annihilator-aware retained cells on every rejected reversible-carrier axis.
This version has no raw intrinsic cardinal-envelope premise: the caller gives
an actual comparator-plus-flag cell map, its uniform cell fibre bound, and the
single numerical capacity inequality charging both the flag and the fibre. -/
noncomputable def
    outsideFrontier_exponentialForwardEstimate_of_axisOwnerOrRetainedCells
    {r : ℕ}
    (Earlier : ∀ d, Fin r → Subgroup (Equiv.Perm (Fin d)) → Prop)
    (hEarlier : DegreeNaturalOwnerMenu Earlier)
    {ρ : ℝ}
    (R : ∀ w, Non2FirstOwnerIndex (r+1) w → Type*)
    [∀ w i, Group (R w i)] [∀ w i, Finite (R w i)]
    (Owned : ∀ w (i : Non2FirstOwnerIndex (r+1) w) (_b : ℕ),
      {N : Subgroup (non2FirstOwnerAction w i) // N.Normal} → Prop)
    (C : ∀ w (i : Non2FirstOwnerIndex (r+1) w) (_b : ℕ),
      {N : Subgroup (non2FirstOwnerAction w i) // N.Normal} → ℝ)
    (A : ∀ w, Non2FirstOwnerIndex (r+1) w → ℝ)
    (v : ∀ w, Non2FirstOwnerIndex (r+1) w → ℕ)
    (η δ c α : ∀ w, Non2FirstOwnerIndex (r+1) w → ℝ)
    (ρR : ∀ w i, R w i →* Equiv.Perm (Fin (v w i)))
    (hρR : ∀ w i, Function.Injective (ρR w i))
    (hC : ∀ w i b N, 0 ≤ C w i b N)
    (hA : ∀ w i, A w i =
      (Nat.card (Subgroup.normalizer
        (non2FirstOwnerAction w i : Set (Equiv.Perm (Fin w)))) : ℝ))
    (hα : ∀ w i, α w i = η w i + c w i)
    (hOwned : ∀ w i b N, Owned w i b N →
      FusionQuotientComparator
        (non2FirstOwnerAction w i) N (R w i))
    (K : ∀ w i N,
      FusionAxisCarrier (non2FirstOwnerAction w i) N)
    (Accepted : ∀ w i b N,
      Subgroup ((K w i N).checked.carrier × Equiv.Perm (Fin b)) → Prop)
    (haccept : ∀ w i b N (J : Subgroup (Equiv.Perm (Fin b)))
        (γ : GroupEpimorphism J (K w i N).checked.quotient),
      (K w i N).checked.carrierInverseSurvival
          (K w i N).source_eq
          (non2FirstOwnerPredicate
            (ownerOrResidualEligible Earlier) w i b)
          (fusionQuotientGraph (K w i N).checked.beta J γ.1) →
        Accepted w i b N
          (fusionQuotientGraph (K w i N).checked.beta J γ.1))
    (Flag : ∀ w (i : Non2FirstOwnerIndex (r+1) w) b
      (_N : {N : Subgroup (non2FirstOwnerAction w i) // N.Normal})
      (_J : Subgroup (Equiv.Perm (Fin b))), Type*)
    (hFlag : ∀ w i b N J, Finite (Flag w i b N J))
    (cell : ∀ w i b N (J : Subgroup (Equiv.Perm (Fin b))),
      FusionCarrierAcceptedEpi (K w i N).checked J (Accepted w i b N) →
        CompleteQuotientMap J (R w i) × Flag w i b N J)
    (Z : ∀ (w) (i : Non2FirstOwnerIndex (r+1) w) (b)
      (_N : {N : Subgroup (non2FirstOwnerAction w i) // N.Normal})
      (_J : Subgroup (Equiv.Perm (Fin b))), ℕ)
    (hcell : ∀ w i b N (J : Subgroup (Equiv.Perm (Fin b)))
        (d : CompleteQuotientMap J (R w i) × Flag w i b N J),
      Nat.card {γ : FusionCarrierAcceptedEpi
          (K w i N).checked J (Accepted w i b N) //
        cell w i b N J γ = d} ≤ Z w i b N J)
    (hcapacity : ∀ w i b N, ¬ Owned w i b N →
      ∀ J : Subgroup (Equiv.Perm (Fin b)),
        (Nat.card (Flag w i b N J) * Z w i b N J : ℕ) ≤
          C w i b N * (2 : ℝ) ^ (η w i * b))
    (hρ : 0 < ρ) (hρ8 : ρ ≤ 1 / 8)
    (hp : GrowingQuotientParameterBound ρ v η δ c α)
    (hmass : GrowingMenuMassBound 3
      (fun w i b => fusionAxisEnvelopeTotal
        (non2FirstOwnerAction w i)
        (fusionOwnerCapacityCoefficient b
          (non2FirstOwnerAction w i) (Owned w i b) (C w i b) (η w i))) A)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ))) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      OrdinaryFrontierClosure.outsideFrontierRatio := by
  apply outsideFrontier_exponentialForwardEstimate_of_axisOwnerOrCarrier
    Earlier hEarlier R Owned C A v η δ c α ρR hρR hC hA hα hOwned
      K Accepted haccept
  · intro w i b N hN J
    letI : Finite (Flag w i b N J) := hFlag w i b N J
    exact fusionCarrierAcceptedEpi_card_le_ownerCapacity_of_retainedCells
      (K w i N).checked J (Accepted w i b N) (cell w i b N J)
      (Z w i b N J) (hcell w i b N J) (C w i b N) (η w i)
      (hcapacity w i b N hN J)
  · exact hρ
  · exact hρ8
  · exact hp
  · exact hmass
  · exact hcoarse

end RepeatedMarkerOwnerBound
end SymmetricSubgroupAsymptotics

end
