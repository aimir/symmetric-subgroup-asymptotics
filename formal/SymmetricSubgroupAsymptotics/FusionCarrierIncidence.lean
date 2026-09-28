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
end SymmetricSubgroupAsymptotics

end
