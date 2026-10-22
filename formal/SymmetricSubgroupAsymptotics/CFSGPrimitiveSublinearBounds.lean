import SymmetricSubgroupAsymptotics.CFSGPrimitiveCoarseDegreeBounds
import SymmetricSubgroupAsymptotics.PrimeCharacterGenerators
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Uniform sublinear composition and normal-subgroup rank for actual
primitive actions from only the displayed simple-group inputs. No sharp
primitive composition or generator theorem is used. -/
set_option autoImplicit false
noncomputable section
open Filter Asymptotics
namespace SymmetricSubgroupAsymptotics.CFSGPrimitiveSublinearBounds
open PrimitiveSocleRawStructure CFSGPrimitiveCoarseDegreeBounds

def coarse (c x : ℝ) : ℝ := (Real.logb 2 x)^2 + c * Real.logb 2 x

theorem coarse_isLittleO (c : ℝ) : (coarse c) =o[atTop] (fun x : ℝ => x) := by
  have hs : (fun x : ℝ => (Real.log x)^2) =o[atTop] (fun x : ℝ => x) := by
    simpa only [Real.rpow_two, Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0 : ℝ) < 1))
  have h := (hs.const_mul_left ((Real.log 2)⁻¹^2)).add
    (Real.isLittleO_log_id_atTop.const_mul_left (c * (Real.log 2)⁻¹))
  convert h using 1
  funext x
  simp only [coarse, Real.logb, div_eq_mul_inv]
  ring

theorem eventually_coarse_le (c : ℝ) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, coarse c n ≤ eps * n := by
  have h := (coarse_isLittleO c).comp_tendsto
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  filter_upwards [h.def heps] with n hn
  simp only [Function.comp_apply, Real.norm_eq_abs] at hn
  have hh : |coarse c n| ≤ eps * n := by
    simpa only [abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)] using hn
  exact (le_abs_self _).trans hh

theorem eventually_primitive_composition (hIndex : PublishedSimpleIndexBounds)
    {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, ∀ (U : Subgroup (Equiv.Perm (Fin n))),
      MulAction.IsPreprimitive U (Fin n) → ∀ s : SubnormalCompositionSeries U,
        (s.chain.length : ℝ) ≤ eps * n := by
  filter_upwards [eventually_coarse_le 3 heps, eventually_ge_atTop 2] with n hb hn
  intro U hp s
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  letI : MulAction.IsPreprimitive U (Fin n) := hp
  have h := primitive_composition_degree_bound (G := U) (X := Fin n) hIndex s
  have hh : (s.chain.length : ℝ) ≤ coarse 3 n := by simpa only [Nat.card_fin, coarse] using h
  exact hh.trans hb

theorem eventually_primitive_normal_rank (hIndex : PublishedSimpleIndexBounds)
    (hGen : FiniteSimpleTwoGeneratorBound) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, ∀ (U : Subgroup (Equiv.Perm (Fin n))),
      MulAction.IsPreprimitive U (Fin n) → ∀ (N : Subgroup U), N.Normal →
        (Group.rank N : ℝ) ≤ eps * n := by
  filter_upwards [eventually_coarse_le 4 heps, eventually_ge_atTop 2] with n hb hn
  intro U hp N hN
  letI := hN
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  letI : MulAction.IsPreprimitive U (Fin n) := hp
  have h := primitive_normal_rank_degree_bound (G := U) (X := Fin n) hIndex hGen N
  have hh : (Group.rank N : ℝ) ≤ coarse 4 n := by simpa only [Nat.card_fin, coarse] using h
  exact hh.trans hb

theorem eventually_c1_primitive_relative_tail (hIndex : PublishedSimpleIndexBounds)
    (hGen : FiniteSimpleTwoGeneratorBound) :
    ∀ᶠ w : ℕ in atTop, ∀ (U : Subgroup (Equiv.Perm (Fin w))),
      MulAction.IsPreprimitive U (Fin w) → ∀ (N : Subgroup U) [N.Normal],
        20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) < 3 * w := by
  filter_upwards [eventually_primitive_normal_rank hIndex hGen
    (by norm_num : (0 : ℝ) < 3/40), eventually_ge_atTop 1] with w hb hw
  intro U hp N hN
  letI := hN
  have hr := hb U hp N hN
  have hc : (Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) : ℝ) ≤ Group.rank N := by
    exact_mod_cast primeRelativeHead_le_groupRank 3 N
  have hwpos : (0 : ℝ) < w := by exact_mod_cast hw
  exact_mod_cast (show (20 : ℝ) * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) < 3 * w by nlinarith)

theorem eventually_primitive_chief_weight (hIndex : PublishedSimpleIndexBounds) :
    ∀ᶠ w : ℕ in atTop, ∀ (U : Subgroup (Equiv.Perm (Fin w))),
      MulAction.IsPreprimitive U (Fin w) → ∀ s : ActualChiefSeries U,
        10 * actualChiefSeriesTernaryWeight s < 3 * w := by
  filter_upwards [eventually_primitive_composition hIndex
    (by norm_num : (0 : ℝ) < 3/20), eventually_ge_atTop 1] with w hb hw
  intro U hp s
  obtain ⟨t, ht⟩ := actualChiefWeight_le_some_compositionLength s
  have hr := hb U hp t
  have hc : (actualChiefSeriesTernaryWeight s : ℝ) ≤ t.chain.length := by exact_mod_cast ht
  have hwpos : (0 : ℝ) < w := by exact_mod_cast hw
  exact_mod_cast (show (10 : ℝ) * actualChiefSeriesTernaryWeight s < 3 * w by nlinarith)

end SymmetricSubgroupAsymptotics.CFSGPrimitiveSublinearBounds
