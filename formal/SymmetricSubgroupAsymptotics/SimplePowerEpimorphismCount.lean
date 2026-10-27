import SymmetricSubgroupAsymptotics.SemisimpleOuterFibre

/-! Every simple-quotient epimorphism, including its automorphism twist,
is counted. The source may be any actual subgroup of a simple power;
it need not be the whole product or a prescribed diagonal chart. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SimplePowerEpimorphismCount

 theorem card_le_of_embedding
    {F T : Type} [Group F] [Finite F] [Group T] [Finite T] [IsSimpleGroup T]
    (hZ : IsCenterless T) (b : ℕ) (rho : F →* (Fin b → T))
    (hrho : Function.Injective rho) :
    (Nat.card (GroupEpimorphism F T) : ℝ) ≤ (b : ℝ)*Nat.card (T ≃* T) := by
  have hcard : Nat.card F≤(Nat.card T)^b := by
    have hh := Nat.card_le_card_of_injective rho hrho
    simpa only [Nat.card_fun,Nat.card_fin] using hh
  have hT : 1<Nat.card T := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  have hL : 0<Real.logb 2 (Nat.card T : ℝ) :=
    Real.logb_pos (by norm_num) (by exact_mod_cast hT)
  have hlog : Real.logb 2 (Nat.card F : ℝ) ≤ (b : ℝ)*Real.logb 2 (Nat.card T : ℝ) := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2)
      (by exact_mod_cast (Nat.card_pos (α := F)))
      (by exact_mod_cast hcard : (Nat.card F : ℝ)≤(Nat.card T : ℝ)^b)
    simpa only [Real.logb_pow] using hh
  have hratio : Real.logb 2 (Nat.card F : ℝ)/Real.logb 2 (Nat.card T : ℝ)≤(b : ℝ) :=
    (div_le_iff₀ hL).mpr hlog
  have hh := simpleGroupEpimorphism_card_le (F := F) (S := T) inferInstance hZ
  have hu := mul_le_mul_of_nonneg_left hratio
    (Nat.cast_nonneg (Nat.card (T ≃* T)))
  exact hh.trans (by simpa only [mul_comm] using hu)

end SymmetricSubgroupAsymptotics.SimplePowerEpimorphismCount
