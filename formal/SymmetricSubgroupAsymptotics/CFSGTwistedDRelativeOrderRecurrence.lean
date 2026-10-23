import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedPoleCharts
import SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankHyperbolicPairs
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTailQuadratic
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPositiveSpace
import SymmetricSubgroupAsymptotics.CFSGTwoAxisChartCardinality
import Mathlib.Algebra.Group.Action.Hom

/-! Explicit fixed singular-vector and companion charts, together with
the literal relative tail embedding, give a lower order recurrence.
Only genuine root-word orbit witnesses are used, in every characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeOrderRecurrence
open CFSGOrthogonalDSerreMatrices CFSGTwistedDRelativeElementaryGroup
open CFSGTwistedDFixedPoleCharts CFSGTwistedDFixedVectorCardinality
open CFSGTwistedDRelativeTailEmbedding CFSGOrthogonalDIndexTailCoordinates
open CFSGTwistedDFixedVectorParametrization

def relativeLinearHom (n : ℕ) (q : CFSG.PrimePower) :
    relativeRootGroup n q →*
      ((Index (n + 2) → q.Extension 2) ≃ₗ[q.Extension 2] (Index (n + 2) → q.Extension 2)) :=
  (CFSGOrthogonalDIndexPositiveSpace.naturalLinearHom (q.Extension 2) (n + 2)).comp
    (Subgroup.inclusion (relativeRootGroup_le_elementary n q))

theorem tail_fixes_pair (n : ℕ) (q : CFSG.PrimePower) (g : relativeRootGroup n q) :
    ((tailRelativeHom n q g).val : Mat (q.Extension 2) (n + 3)) *ᵥ
        Pi.single (Sum.inl 0) 1 = Pi.single (Sum.inl 0) 1 ∧
      ((tailRelativeHom n q g).val : Mat (q.Extension 2) (n + 3)) *ᵥ
        Pi.single (Sum.inr 0) 1 = Pi.single (Sum.inr 0) 1 := by
  let K := q.Extension 2
  have haxis (j : Fin 2) :
      ((tailRelativeHom n q g).val : Mat K (n + 3)) *ᵥ
          Pi.single (tailEquiv (n + 2) (Sum.inr j)) 1 =
        Pi.single (tailEquiv (n + 2) (Sum.inr j)) 1 := by
    rw [Matrix.mulVec_single_one]
    funext x
    obtain ⟨x, rfl⟩ := (tailEquiv (n + 2)).surjective x
    change tailMatrixHom K (n + 2) (g.val : Mat K (n + 2))
      (tailEquiv (n + 2) x) (tailEquiv (n + 2) (Sum.inr j)) = _
    rw [tailMatrixHom_apply_equiv]
    cases x with
    | inl i =>
      have hn : tailEquiv (n + 2) (Sum.inl i) ≠ tailEquiv (n + 2) (Sum.inr j) := by
        intro h
        cases (tailEquiv (n + 2)).injective h
      simp only [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, Pi.single_eq_of_ne hn]
    | inr i =>
      simp only [Matrix.fromBlocks_apply₂₂, Matrix.one_apply, Pi.single_apply,
        (tailEquiv (n + 2)).injective.eq_iff, Sum.inr.injEq]
  exact ⟨haxis 0, haxis 1⟩

theorem relative_card_lower_step (n : ℕ) (q : CFSG.PrimePower) :
    q.order ^ (4 * (n + 2)) * Nat.card (relativeRootGroup n q) ≤
      Nat.card (relativeRootGroup (n + 1) q) := by
  let K := q.Extension 2
  let G := relativeRootGroup (n + 1) q
  let V := Index (n + 3) → K
  letI : DistribMulAction G V := DistribMulAction.compHom V (relativeLinearHom (n + 1) q)
  let e : V := Pi.single (Sum.inl 0) 1
  let f : V := Pi.single (Sum.inr 0) 1
  have hs (w : fixedVectors n q) : ∃ g : G, g • e = positiveChart n q w := by
    have hw0 : positiveChart n q w ≠ 0 := by
      intro h
      have he := congrFun h (Sum.inl 0)
      exact one_ne_zero he
    obtain ⟨a, ha⟩ := CFSGTwistedDAllRankSingularOrbit.exists_normalize_all (n + 1) q
      (positiveChart n q w) (positiveChart_fixed n q w) (positiveChart_singular n q w) hw0
    refine ⟨a⁻¹, ?_⟩
    change (↑(a.val⁻¹) : Mat K (n + 3)) *ᵥ Pi.single (Sum.inl 0) 1 = _
    rw [← ha, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have ht (w : fixedVectors n q) : ∃ g : G, g • e = e ∧ g • f = negativeChart n q w := by
    obtain ⟨a, he, hf⟩ := CFSGTwistedDAllRankHyperbolicPairs.exists_normalize_companion_all
      (n + 1) q (negativeChart n q w) (negativeChart_fixed n q w)
      (negativeChart_singular n q w) (negativeChart_last n q w)
    refine ⟨a⁻¹, ?_, ?_⟩
    · change (↑(a.val⁻¹) : Mat K (n + 3)) *ᵥ Pi.single (Sum.inl 0) 1 = _
      rw [← he, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    · change (↑(a.val⁻¹) : Mat K (n + 3)) *ᵥ Pi.single (Sum.inr 0) 1 = _
      rw [← hf, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hfix (g : relativeRootGroup n q) :
      tailRelativeHom n q g • e = e ∧ tailRelativeHom n q g • f = f :=
    tail_fixes_pair n q g
  have h := CFSGTwoAxisChartCardinality.product_card_le e f
    (positiveChart n q) (negativeChart n q) (positiveChart_injective n q)
    (negativeChart_injective n q) hs ht (tailRelativeHom n q) (tailRelativeHom_injective n q) hfix
  rw [fixedVectors_card] at h
  have he : q.order ^ (2 * (n + 2)) *
        (q.order ^ (2 * (n + 2)) * Nat.card (relativeRootGroup n q)) =
      q.order ^ (4 * (n + 2)) * Nat.card (relativeRootGroup n q) := by
    rw [← mul_assoc, ← pow_add]
    congr 2
    omega
  exact he ▸ h

theorem relative_card_two_steps (s : ℕ) (q : CFSG.PrimePower) :
    q.order ^ (8 * s + 20) ≤ Nat.card (relativeRootGroup (s + 2) q) := by
  have h0 : 1 ≤ Nat.card (relativeRootGroup s q) := Nat.card_pos
  have h1 := relative_card_lower_step s q
  have h2 := relative_card_lower_step (s + 1) q
  have h3 : q.order ^ (4 * (s + 2)) ≤ Nat.card (relativeRootGroup (s + 1) q) :=
    by simpa only [mul_one] using
      (Nat.mul_le_mul_left (q.order ^ (4 * (s + 2))) h0).trans h1
  have h4 := (Nat.mul_le_mul_left (q.order ^ (4 * (s + 1 + 2))) h3).trans h2
  rw [← pow_add] at h4
  convert h4 using 1 <;> congr 1 <;> omega

end SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeOrderRecurrence
