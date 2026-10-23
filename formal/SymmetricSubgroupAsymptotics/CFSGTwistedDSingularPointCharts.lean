import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedQuadraticSpace
import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedVectorParametrization

/-! A literal affine chart of normalized singular points in every
actual defining-fixed space, including the elliptic rank-two base.
The chart contains q^(2(n+1)) distinct points in natural rank n+2.
No orthogonal order or singular-point census is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDSingularPointCharts
open CFSGOrthogonalDSerreMatrices CFSGTwistedDFixedQuadraticSpace
open CFSGTwistedDFixedVectorParametrization CFSGTwistedDFixedVectorCardinality
open CFSGTwistedDFixedPoleCharts CFSGTwistedA2FixedField CFSGSerreOrdinaryTwists
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexQuadraticForm

private def normValue (q : CFSG.PrimePower) (a : q.Extension 2) : fixedField q :=
  ⟨a * definingFieldAutomorphism q 2 a, by
    change definingFieldAutomorphism q 2 (a * definingFieldAutomorphism q 2 a) =
      a * definingFieldAutomorphism q 2 a
    have hs : definingFieldAutomorphism q 2 (definingFieldAutomorphism q 2 a) = a :=
      CFSGTwistedANaturalMatrices.extension_two_pow_twice q a
    rw [map_mul, hs]
    exact mul_comm _ _⟩

def baseChart (q : CFSG.PrimePower) (a : q.Extension 2) : fixedSpace 0 q :=
  ⟨fromParameters 0 q ((fun _ => -normValue q a), ((fun _ => 1), a)),
    fromParameters_fixed 0 q _⟩

def Parameters : (n : ℕ) → (q : CFSG.PrimePower) → Type
  | 0, q => q.Extension 2
  | n + 1, q => fixedVectors n q

def chart : (n : ℕ) → (q : CFSG.PrimePower) → Parameters n q → fixedSpace n q
  | 0, q, a => baseChart q a
  | n + 1, q, w => ⟨negativeChart n q w, negativeChart_fixed n q w⟩

theorem chart_normalized (n : ℕ) (q : CFSG.PrimePower) (a : Parameters n q) :
    (chart n q a).val (Sum.inr 0) = 1 := by
  cases n with
  | zero => rfl
  | succ n => exact negativeChart_last n q a

theorem chart_singular (n : ℕ) (q : CFSG.PrimePower) (a : Parameters n q) :
    fixedQuadraticForm n q (chart n q a) = 0 := by
  apply Subtype.ext
  rw [fixedQuadraticForm_apply]
  cases n with
  | zero =>
    rw [splitQuadraticForm_apply]
    change (∑ i : Fin 2, (baseChart q a).val (Sum.inl i) *
      (baseChart q a).val (Sum.inr i)) = 0
    rw [Fin.sum_univ_two]
    let a0 : q.Extension 2 := a
    change (-(a0 * definingFieldAutomorphism q 2 a0)) * 1 +
      a0 * definingFieldAutomorphism q 2 a0 = 0
    ring
  | succ n => exact negativeChart_singular n q a

theorem chart_nonzero (n : ℕ) (q : CFSG.PrimePower) (a : Parameters n q) : chart n q a ≠ 0 := by
  intro he
  have hx := congrArg (fun v : fixedSpace n q => v.val (Sum.inr 0)) he
  dsimp only at hx
  rw [chart_normalized] at hx
  exact one_ne_zero hx

theorem chart_injective (n : ℕ) (q : CFSG.PrimePower) : Function.Injective (chart n q) := by
  cases n with
  | zero =>
    intro a b he
    exact congrArg (fun v : fixedSpace 0 q => v.val (Sum.inl (1 : Fin 2))) he
  | succ n =>
    intro a b he
    exact negativeChart_injective n q (congrArg Subtype.val he)

theorem parameters_card (n : ℕ) (q : CFSG.PrimePower) :
    Nat.card (Parameters n q) = q.order ^ (2 * (n + 1)) := by
  cases n with
  | zero => exact CFSGTwistedANaturalMatrices.extension_two_card q
  | succ n =>
    exact fixedVectors_card n q

theorem chart_span_injective (n : ℕ) (q : CFSG.PrimePower) :
    Function.Injective (fun a : Parameters n q =>
      Submodule.span (fixedField q) {chart n q a}) := by
  intro a b he
  dsimp only at he
  have hm : chart n q a ∈ Submodule.span (fixedField q) {chart n q b} := by
    rw [← he]
    exact Submodule.subset_span (Set.mem_singleton _)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
  have hv := congrArg (fun v : fixedSpace n q => v.val (Sum.inr 0)) hc
  change (c : q.Extension 2) * (chart n q b).val (Sum.inr 0) =
    (chart n q a).val (Sum.inr 0) at hv
  rw [chart_normalized, chart_normalized, mul_one] at hv
  have hc1 : c = 1 := Subtype.ext hv
  rw [hc1, one_smul] at hc
  exact chart_injective n q hc.symm

end SymmetricSubgroupAsymptotics.CFSGTwistedDSingularPointCharts
