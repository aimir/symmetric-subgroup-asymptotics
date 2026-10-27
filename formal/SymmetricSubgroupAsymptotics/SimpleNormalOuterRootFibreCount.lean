import SymmetricSubgroupAsymptotics.SemisimpleOuterFibre
import SymmetricSubgroupAsymptotics.CFSGFiniteFamilyGeneration
import SymmetricSubgroupAsymptotics.MarkedC4GeneratorNumbers

/-! Exact root fibres for twisted local maps reuse the proved semisimple
outer fibre. Every map is onto the same actual local U/N, with the same
literal outer map. The simple image is transported through an actual chart.
No untwisted action, model order or numerical outer bound is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SimpleNormalOuterRootFibreCount

variable {U J T : Type*} [Group U] [Finite U] [Group J] [Finite J]
    [Group T] [Finite T] [IsSimpleGroup T]
variable {E : Subgroup U} [E.Normal] (C : SemisimpleNormalChart E)
    (N : {N : Subgroup U // N.Normal})
    (θ : GroupEpimorphism J (U ⧸ (N.val⊔E)))
    (e : quotientImage E N ≃* T) (hZ : IsCenterless T)

include C e hZ in
theorem card_root_fibre_le :
    (Nat.card {φ : GroupEpimorphism J (U ⧸ N.val) //
      (quotientOuter E N).comp φ.val=θ.val} : ℝ) ≤
      Nat.card (T ≃* T)*
        (Real.logb 2 (Nat.card θ.val.ker)/Real.logb 2 (Nat.card T)) := by
  have hf := C.fibre_card_le N θ
  have he : Nat.card (GroupEpimorphism θ.val.ker (quotientImage E N))=
      Nat.card (GroupEpimorphism θ.val.ker T) :=
    fusionGroupEpimorphism_card_congr (MulEquiv.refl θ.val.ker) e
  rw [he] at hf
  have hh := simpleGroupEpimorphism_card_le (F := θ.val.ker) (S := T) inferInstance hZ
  exact (show (Nat.card {φ : GroupEpimorphism J (U ⧸ N.val) //
      (quotientOuter E N).comp φ.val=θ.val} : ℝ) ≤
      (Nat.card (GroupEpimorphism θ.val.ker T) : ℝ) by exact_mod_cast hf).trans hh

theorem aut_card_le_rank_power : Nat.card (T ≃* T)≤Nat.card T^MarkedC4.genRank T := by
  obtain ⟨S,hcard,hS⟩ := MarkedC4.genRank_spec (G := T)
  exact CFSGGeneration.aut_card_le_pow_of_generators S hS hcard.le

include C e hZ in
theorem card_root_fibre_le_rank_power :
    (Nat.card {φ : GroupEpimorphism J (U ⧸ N.val) //
      (quotientOuter E N).comp φ.val=θ.val} : ℝ) ≤
      (Nat.card T : ℝ)^MarkedC4.genRank T*
        (Real.logb 2 (Nat.card θ.val.ker)/Real.logb 2 (Nat.card T)) := by
  have hlog : 0≤Real.logb 2 (Nat.card θ.val.ker : ℝ) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1≤Nat.card θ.val.ker from Nat.card_pos))
  have hlogT : 0≤Real.logb 2 (Nat.card T : ℝ) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1≤Nat.card T from Nat.card_pos))
  have ha : (Nat.card (T ≃* T) : ℝ)≤(Nat.card T : ℝ)^MarkedC4.genRank T := by
    exact_mod_cast (aut_card_le_rank_power (T := T))
  exact (card_root_fibre_le C N θ e hZ).trans
    (mul_le_mul_of_nonneg_right ha (div_nonneg hlog hlogT))

end SymmetricSubgroupAsymptotics.SimpleNormalOuterRootFibreCount
