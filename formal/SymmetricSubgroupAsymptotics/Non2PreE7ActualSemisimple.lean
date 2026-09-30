import SymmetricSubgroupAsymptotics.Non2PreE7SemisimpleTemplate

/-!
# The SS family: an actual semisimple action

For a literal action which is itself a nontrivial product of centerless
simple factors, the outer quotient is trivial.  The semisimple outer-fibre
product therefore gives the complete all-source envelope directly, with
zero linear source exponent.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

structure PreE7SsActionCertificate
    (w : ℕ) (i : PreE7NonPairActionClass w) where
  width_lower : 5 ≤ w
  chart : SemisimpleNormalChart
    (⊤ : Subgroup (preE7NonPairAction w i))
  layer_ne_bot : (⊤ : Subgroup (preE7NonPairAction w i)) ≠ ⊥
  coefficient_total_bound : ∀ b,
    fusionAxisEnvelopeTotal (preE7NonPairAction w i)
        (fun _ => chart.outerFactor (Real.logb 2 (Nat.factorial b))) ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)

namespace PreE7SsActionCertificate

variable {w : ℕ} {i : PreE7NonPairActionClass w}
  (C : PreE7SsActionCertificate w i)

def coefficient (b : ℕ) : ℝ :=
  C.chart.outerFactor (Real.logb 2 (Nat.factorial b))

def degree (_C : PreE7SsActionCertificate w i) : ℕ :=
  paddedComparatorDegree preE7CharacterRho 2 w

def delta (_C : PreE7SsActionCertificate w i) : ℝ :=
  paddedComparatorDelta preE7CharacterRho 0 2 w

def cutoff : ℝ := (C.degree : ℝ) / 8 + C.delta / 2

theorem coefficient_nonneg (b : ℕ) : 0 ≤ C.coefficient b :=
  C.chart.outerFactor_nonneg (Real.logb_nonneg (by norm_num)
    (by exact_mod_cast Nat.factorial_pos b))

theorem degree_margin (C : PreE7SsActionCertificate w i) :
    preE7CharacterRho * w ≤ ((evenWidth w : ℝ) - 2) / 8 := by
  have heven : (w : ℝ) ≤ evenWidth w + 1 := by
    exact_mod_cast width_le_evenWidth_add_one w
  have hw : (5 : ℝ) ≤ w := by exact_mod_cast C.width_lower
  unfold preE7CharacterRho
  norm_num
  linarith

private theorem log_source_le_factorial
    (_C : PreE7SsActionCertificate w i) (b : ℕ)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    Real.logb 2 (Nat.card J) ≤ Real.logb 2 (Nat.factorial b) := by
  apply Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast Nat.card_pos)
  have hcard := Nat.card_le_card_of_injective
    (Subtype.val : J → Equiv.Perm (Fin b)) Subtype.val_injective
  rw [Nat.card_perm, Nat.card_fin] at hcard
  exact_mod_cast hcard

/-- The exact direct semisimple datum used by the common owner template. -/
noncomputable def direct :
    PreE7SemisimpleDirectSourceData .ss w i := by
  classical
  let U := preE7NonPairAction w i
  exact
    { template_eq := rfl
      E := ⊤
      E_normal := inferInstance
      chart := C.chart
      v := C.degree
      coefficient := C.coefficient
      eta := 0
      delta := C.delta
      cutoff := C.cutoff
      alpha := C.cutoff
      theta := 0
      alpha_eq := by simp
      coefficient_nonneg := C.coefficient_nonneg
      coefficient_total_bound := C.coefficient_total_bound
      combined_bound := by
        intro b J
        letI := QuotientGroup.subsingleton_quotient_top (G := U)
        rw [completeQuotientWeight_eq_one_of_subsingleton
          (R := U ⧸ (⊤ : Subgroup U)) J, one_mul]
        have hprod :
            C.chart.outerFactor (Real.logb 2 (Nat.card J)) ≤
              C.chart.outerFactor (Real.logb 2 (Nat.factorial b)) := by
          unfold SemisimpleNormalChart.outerFactor
          apply Finset.prod_le_prod
          · intro k _
            exact add_nonneg zero_le_one
              (C.chart.factorWeight_nonneg
                (Real.logb_nonneg (by norm_num)
                  (by exact_mod_cast Nat.card_pos)) k)
          · intro k _
            simpa only [add_comm] using add_le_add_left
              (C.chart.factorWeight_mono
                (C.log_source_le_factorial b J) k) 1
        simpa only [zero_mul, Real.rpow_zero, mul_one] using hprod }

end PreE7SsActionCertificate

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
