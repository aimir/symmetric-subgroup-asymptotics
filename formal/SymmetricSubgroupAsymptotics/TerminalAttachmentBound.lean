import SymmetricSubgroupAsymptotics.TerminalImageCounts
import SymmetricSubgroupAsymptotics.TerminalDivisorArithmetic

/-! Actual complete-exterior terminal attachment from original record fibres. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics
attribute [local instance] Fintype.ofFinite

local instance {D F : Type*} [AddCommGroup D] [Module (ZMod 2) D]
    [AddCommGroup F] [Module (ZMod 2) F] [Finite D] [Finite F] :
    Finite (D →ₗ[ZMod 2] F) :=
  Finite.of_injective DFunLike.coe DFunLike.coe_injective

variable {ι : Type} [Fintype ι] (a : ℕ) (s : ι → Bool)
  (T : Type) [Group T] [Finite T]

/-- Dropping only vertical injectivity enlarges the nonnegative exact
original record sum. Changing the fixed quotient basis is bijective. -/
theorem terminalOriginalOrderedWeight_le (u : ℕ) :
    (∑ p : TerminalOrderedMaps (A := BinaryAbelianization T)
      (V := Fin (criticalProductRank a s) → ZMod 2) u,
        terminalOriginalImageWeight a s T (terminalRawRecordGroupMap u p.1).range) ≤
      terminalCriticalWeightedMaps a s u T := by
  let w := fun p : ((Fin u → ZMod 2) × BinaryAbelianization T) →ₗ[ZMod 2]
      (Fin (criticalProductRank a s) → ZMod 2) =>
    if ∀ i, Function.Surjective (fun x => (terminalRecordPhysicalMap a s u T p x).2 i) then
      terminalCriticalMapWeight a s u T (terminalRecordPhysicalMap a s u T p) else 0
  have hw (p) : 0 ≤ w p := by
    dsimp [w]
    split_ifs
    · exact terminalCriticalMapWeight_nonneg a s u T _
    · exact le_rfl
  calc
    _ = ∑ p : TerminalOrderedMaps (A := BinaryAbelianization T)
        (V := Fin (criticalProductRank a s) → ZMod 2) u, w p.1 := by
      apply Finset.sum_congr rfl
      intro p _
      exact terminalOriginalImageWeight_record a s T u p
    _ ≤ ∑ p : ((Fin u → ZMod 2) × BinaryAbelianization T) →ₗ[ZMod 2]
        (Fin (criticalProductRank a s) → ZMod 2), w p := by
      have h := Fintype.sum_subtype_add_sum_subtype
        (fun p : ((Fin u → ZMod 2) × BinaryAbelianization T) →ₗ[ZMod 2]
          (Fin (criticalProductRank a s) → ZMod 2) =>
          Function.Injective (p.comp (LinearMap.inl _ _ _))) w
      have hn : 0 ≤ ∑ p : {p : ((Fin u → ZMod 2) × BinaryAbelianization T) →ₗ[ZMod 2]
          (Fin (criticalProductRank a s) → ZMod 2) //
          ¬ Function.Injective (p.comp (LinearMap.inl _ _ _))}, w p.1 :=
        Finset.sum_nonneg (fun p _ => hw p.1)
      exact (le_add_of_nonneg_right hn).trans h.le
    _ = _ := by
      exact Fintype.sum_equiv
        (LinearEquiv.congrRight (criticalProductChart a s)).toEquiv _ _ (fun _ => rfl)

/-- Division by every original ordered basis and every original lift,
before applying any incidence estimate. -/
theorem terminalRankImageWeight_le (u : ℕ) :
    (∑ U : {U : Submodule (ZMod 2) (Fin (criticalProductRank a s) → ZMod 2) //
        Module.finrank (ZMod 2) U=u},
      ∑ f : BinaryAbelianization T →ₗ[ZMod 2] (Fin (criticalProductRank a s) → ZMod 2) ⧸ U.1,
        terminalOriginalImageWeight a s T (terminalLinearQuotientGraph U.1 f)) ≤
      terminalCriticalWeightedMaps a s u T / (terminalRecordDivisor u (binaryCharacterRank T) : ℝ) := by
  have hd : (0 : ℝ) < (terminalRecordDivisor u (binaryCharacterRank T) : ℝ) := by
    exact_mod_cast terminalRecordDivisor_pos u (binaryCharacterRank T)
  have he := terminalRankRecords_weight_sum
    (V := Fin (criticalProductRank a s) → ZMod 2) (T := T) u
    (terminalOriginalImageWeight a s T)
  have hb := terminalOriginalOrderedWeight_le a s T u
  apply (le_div_iff₀ hd).mpr
  rw [mul_comm]
  calc
    _ = _ := he.symm
    _ = _ := Fintype.sum_equiv (Equiv.refl _) _ _ (fun _ => rfl)
    _ ≤ _ := hb

/-- The complete central incidence sum after the original record divisor. -/
theorem terminalRankImageWeight_le_incidence (u : ℕ) :
    (∑ U : {U : Submodule (ZMod 2) (Fin (criticalProductRank a s) → ZMod 2) //
        Module.finrank (ZMod 2) U=u},
      ∑ f : BinaryAbelianization T →ₗ[ZMod 2] (Fin (criticalProductRank a s) → ZMod 2) ⧸ U.1,
        terminalOriginalImageWeight a s T (terminalLinearQuotientGraph U.1 f)) ≤
      ∑ l ∈ Finset.range (Fintype.card ι+1),
        terminalRecordIncidenceTerm (criticalProductRank a s) (Fintype.card ι)
          (binaryCharacterRank T) (Module.finrank (ZMod 2) (terminalRestrictedInflationKernel T)) u l := by
  refine (terminalRankImageWeight_le a s T u).trans ?_
  have hd : (0 : ℝ) ≤ (terminalRecordDivisor u (binaryCharacterRank T) : ℝ) := by positivity
  have h := div_le_div_of_nonneg_right (terminalCriticalWeightedMaps_le a s u T) hd
  simpa only [terminalRecordIncidenceTerm,Finset.sum_div] using h

/-- Every nonabelian critical factor contributes at least two quotient
dimensions, including an empty nonabelian index set. -/
theorem terminalCritical_two_card_le_rank : 2*Fintype.card ι ≤ criticalProductRank a s := by
  have h : (∑ i : ι, 2) ≤ ∑ i : ι, criticalFactorRank (s i) := by
    apply Finset.sum_le_sum
    intro i _
    cases s i <;> simp [criticalFactorRank]
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul] at h
  unfold criticalProductRank
  omega

/-- Unconditional complete-exterior terminal bound for literal subgroups.
The exterior may be nonabelian. Every original nonabelian factor is full;
any additional regular C2/V4 fullness requirements select a subfamily.
The parameter is the actual retained H² inflation kernel of this T. -/
theorem terminalActualSubgroups_card_le_doubleSum :
    (Nat.card (TerminalActualSubgroups a s T) : ℝ) ≤
      terminalGaussianDoubleSum (criticalProductRank a s) (Fintype.card ι)
        (binaryCharacterRank T) (Module.finrank (ZMod 2) (terminalRestrictedInflationKernel T)) := by
  refine (terminalActualSubgroups_card_le_graphs a s T).trans ?_
  rw [binary_subspace_sum_by_rank]
  simp only [Module.finrank_pi,Fintype.card_fin]
  refine le_trans (Finset.sum_le_sum (fun u _ => terminalRankImageWeight_le_incidence a s T u)) ?_
  exact terminalRecordIncidenceSum_le _ _ _ _ (terminalCritical_two_card_le_rank a s)

/-- Any further literal fullness or incidence condition on the original
subgroups is retained by taking its actual subfamily. -/
theorem terminalActualSubfamily_card_le_doubleSum
    (P : Subgroup (CriticalProductGroup a s × T) → Prop) :
    (Nat.card {H : TerminalActualSubgroups a s T // P H.1} : ℝ) ≤
      terminalGaussianDoubleSum (criticalProductRank a s) (Fintype.card ι)
        (binaryCharacterRank T) (Module.finrank (ZMod 2) (terminalRestrictedInflationKernel T)) := by
  refine le_trans ?_ (terminalActualSubgroups_card_le_doubleSum a s T)
  exact_mod_cast Nat.card_le_card_of_injective
    (fun H : {H : TerminalActualSubgroups a s T // P H.1} => H.1) Subtype.val_injective

end SymmetricSubgroupAsymptotics
