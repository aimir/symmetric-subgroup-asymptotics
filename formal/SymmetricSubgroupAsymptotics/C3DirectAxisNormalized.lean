import SymmetricSubgroupAsymptotics.C3DirectAxisCount
import SymmetricSubgroupAsymptotics.FusionArbitraryWidth

/-!
# The direct-axis regular C3 row

The full first-axis branch is a literal direct product.  Its complete local
count is therefore at most the subgroup count on the untouched complement.
After the original normalizer divisor six and exact benchmark normalization,
the resulting width-three row has a uniform exponential contraction.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- The full accepted local family with full first Goursat axis. -/
def C3DirectAxisPredicate (b : ℕ)
    (P : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)) → Prop)
    (H : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b))) : Prop :=
  FusionAcceptedOrbitPredicate ternaryRegularAction P H ∧ H.goursatFst = ⊤

def c3DirectAxisPredicateEquiv (b : ℕ)
    (P : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)) → Prop) :
    {H // C3DirectAxisPredicate b P H} ≃ C3DirectAxisLocalFamily P where
  toFun H := ⟨⟨H.1,H.2.1⟩,H.2.2⟩
  invFun H := ⟨H.1.1,H.1.2,H.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem c3DirectAxisPredicate_card_le (b : ℕ)
    (P : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)) → Prop) :
    Nat.card {H // C3DirectAxisPredicate b P H} ≤ subgroupCount b := by
  rw [Nat.card_congr (c3DirectAxisPredicateEquiv b P)]
  exact c3DirectAxis_card_le_subgroupCount b P

/-- Naturality of the direct-axis family retains the arbitrary complete
survival predicate. -/
theorem c3DirectAxisPredicate_natural (b : ℕ)
    (P : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)) → Prop)
    (hP : FusionOrbitNatural ternaryRegularAction P) :
    FusionOrbitNatural ternaryRegularAction (C3DirectAxisPredicate b P) := by
  rintro c H ⟨⟨hfull,hPsurvives⟩,haxis⟩
  refine ⟨⟨fusion_full_map_prod H hfull
    (ternaryRegularAction.normalizerMonoidHom c.1) (MulAut.conj c.2),
      hP c H hPsurvives⟩,?_⟩
  change (H.map (((ternaryRegularAction.normalizerMonoidHom c.1).prodCongr
    (MulAut.conj c.2)).toMonoidHom)).goursatFst = ⊤
  rw [fusion_axis_map_prod,haxis]
  exact Subgroup.map_top_of_surjective _
    (ternaryRegularAction.normalizerMonoidHom c.1).surjective

/-- Original physical pointing gives the complete direct-axis row with the
actual regular-C3 normalizer divisor. -/
theorem c3DirectAxis_physical_card_le (b : ℕ)
    (P : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)) → Prop)
    (hP : FusionOrbitNatural ternaryRegularAction P) :
    (Nat.card (FusionOrbitFamily ternaryRegularAction
      (C3DirectAxisPredicate b P)) : ℝ) ≤
        ((b+3).factorial : ℝ) / (6*b.factorial) * subgroupCount b := by
  have h := fusionOrbitFamily_card_le ternaryRegularAction
    (C3DirectAxisPredicate b P) (c3DirectAxisPredicate_natural b P hP)
  have hc : (Nat.card {H // C3DirectAxisPredicate b P H} : ℝ) ≤
      subgroupCount b := by
    exact_mod_cast c3DirectAxisPredicate_card_le b P
  rw [ternaryRegularAction_normalizer_card] at h
  simp only [TernaryCyclic,Fintype.card_multiplicative,ZMod.card,Fintype.card_fin,
    Nat.cast_ofNat] at h
  calc
    _ ≤ ((3+b).factorial : ℝ) / (b.factorial*6) *
        Nat.card {H // C3DirectAxisPredicate b P H} := h
    _ ≤ ((3+b).factorial : ℝ) / (b.factorial*6) * subgroupCount b :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by rw [Nat.add_comm 3 b]; ring

def c3DirectAxisKernel (b : ℕ) : ℝ :=
  fusionWidthColdKernel b 3 1 6 0

theorem c3DirectAxisKernel_nonneg (b : ℕ) : 0 ≤ c3DirectAxisKernel b :=
  fusionWidthColdKernel_nonneg b 3 (by norm_num) (by norm_num)

theorem c3DirectAxisKernel_eventually :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ b : ℕ in atTop,
      c3DirectAxisKernel b ≤ C*(2:ℝ)^(-(1/8:ℝ)*b) := by
  simpa only [c3DirectAxisKernel,halfDegree,
    show (3:ℕ)/2=1 by decide,Nat.cast_one,
    show (((1:ℝ)/4-0)/2)=1/8 by norm_num] using
    fusionWidthColdKernel_eventually 3 (D := 1) (a := 6) (α := 0)
      (by norm_num) (by norm_num) (by norm_num [halfDegree])

/-- Exact normalization of the direct-axis row against the original
benchmark.  No estimate for the normalized lower-degree subgroup count is
used. -/
theorem c3DirectAxis_physical_normalized (b : ℕ)
    (P : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)) → Prop)
    (hP : FusionOrbitNatural ternaryRegularAction P) :
    (Nat.card (FusionOrbitFamily ternaryRegularAction
      (C3DirectAxisPredicate b P)) : ℝ) / exactBenchmark (b+3) ≤
        c3DirectAxisKernel b *
          ((subgroupCount b:ℝ)/exactBenchmark b) := by
  have hL := exactBenchmark_pos b
  have hN := exactBenchmark_pos (b+3)
  have h := div_le_div_of_nonneg_right (c3DirectAxis_physical_card_le b P hP) hN.le
  apply h.trans_eq
  unfold c3DirectAxisKernel fusionWidthColdKernel fusionWidthPointingRatio
  simp only [zero_mul,Real.rpow_zero,mul_one]
  field_simp

end SymmetricSubgroupAsymptotics

end
