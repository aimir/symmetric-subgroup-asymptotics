import SymmetricSubgroupAsymptotics.MarkedC4ActualBoundedBinaryError
import SymmetricSubgroupAsymptotics.MarkedC4OrdinarySubgroupUpper
import SymmetricSubgroupAsymptotics.ConstructedBoundedCoreFixedCutoffReduction

/-! Constructed fixed-cutoff marked theorem. The actual binary-word
history bound and ordinary odd subgroup estimate are composed with the
proved relative nilpotent and physical product reductions. -/
set_option autoImplicit false
noncomputable section
open Filter
namespace SymmetricSubgroupAsymptotics.MarkedC4.BoundedCoreFixedCutoffMarkedBound
open RDTOriginalWordStructure RDTNormalFInterface OrdinaryNilpotentGeneration

theorem marked_bound
    (hgen : KovacsPraegerAbelianizationBound)
    (hKP : KovacsPraegerBinaryAbelianQuotientBound) (h55 : PublishedTheorem55Binary)
    (h53 : ActualCaseIITargetStructure.PublishedProposition53Binary)
    (h57 : RDTExcessStructure.PublishedTheorem57Binary)
    (h8 : RDTDegreeEightExceptional.PublishedDegreeEightExceptional)
    (hderived : RDTDerivedNormalQuarter.PublishedDerivedNormalQuarterBinary)
    (lit : RDTTheorem46BinaryInput)
    (hodd : OrdinarySubgroupUpper.PublishedTheoremOneUpper)
    {C : ℕ} (hC : 1<C) :
    ∀ ε : ℝ,0<ε → ∀ K : ℝ,∀ᶠ b : ℕ in atTop,∀ r : ℕ,
      (r : ℝ)≤K*b → OrbitCutoffFamilies.solubleCount C b r ≤
        (2 : ℝ)^(markedF b r+ε*((b : ℝ)+r)^2) := by
  obtain ⟨β,hβ,hoddβ⟩ := OrdinarySubgroupUpper.exists_nonnegative_coarse hodd
  let E := ActualBoundedBinaryError.error lit C
  let R := (ConstructedBoundedCoreFixedCutoffReduction.reduction hgen hC).toMarkedMomentReduction.error
  apply markedMomentBound_of_error (e := fun b r => R b r+E b r+
    PhysicalOddConvolution.coarseError β b+boundedWordError 1 b r)
  · intro b r
    have hc := ConstructedBoundedCoreFixedCutoffReduction.count_le_convolution hgen hC b r
    have hb := PhysicalOddConvolution.bound
      (binary := BoundedNilpotentTargetConvolution.binaryMoment C)
      (odd := NilpotentTargetConvolution.oddCount) (E := E) (C := β) hβ
      (fun a s => by unfold BoundedNilpotentTargetConvolution.binaryMoment; positivity)
      (fun d => Nat.cast_nonneg _) 
      (ActualBoundedBinaryError.marked_bound hKP h55 h53 h57 h8 hderived lit C)
      hoddβ (ActualBoundedBinaryError.mono lit C) b r
    apply hc.trans
    calc
      _ ≤ (2 : ℝ)^R b r *
          (2 : ℝ)^(markedF b r+E b r+PhysicalOddConvolution.coarseError β b+boundedWordError 1 b r) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ)<2)]
        congr 1
        ring
  · exact (((ConstructedBoundedCoreFixedCutoffReduction.error_negligible hgen hC).add
      (ActualBoundedBinaryError.negligible lit C)).add
        (PhysicalOddConvolution.coarseError_negligible hβ)).add
          (boundedWordError_negligible (by norm_num))

end SymmetricSubgroupAsymptotics.MarkedC4.BoundedCoreFixedCutoffMarkedBound
end
