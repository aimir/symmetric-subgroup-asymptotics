import SymmetricSubgroupAsymptotics.ProjectiveLinearPrimeDivisor
import SymmetricSubgroupAsymptotics.CFSGTypeARankTwoCardTwo
import SymmetricSubgroupAsymptotics.CFSGTypeARankTwoClassCube
import Mathlib.Data.Nat.Prime.Int

/-! Thirteen divides the SAME original rank-two projective model over
any three-element field. Its faithful simple coset action gives index
at least thirteen; the proved class and outer bounds then pay the scaled
packet. Only finite-field matrix order metadata is evaluated. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeARankTwoCardThree
open PrimitiveSocleRawStructure

theorem thirteen_dvd_projective_card (F : Type*) [Field F] [Finite F]
    (hF : Nat.card F=3) :
    13 ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) := by
  letI : Fintype F := Fintype.ofFinite F
  have hu : Nat.card Fˣ=2 := by rw [Nat.card_units,hF]
  apply ProjectiveLinearPrimeDivisor.dvd_projective_of_dvd_general 13 (by decide)
    (by rw [hu]; decide)
  rw [Matrix.card_GL_field]
  have hf : Fintype.card F=3 := by simpa only [Nat.card_eq_fintype_card] using hF
  rw [hf]
  norm_num [Fin.prod_univ_three]

theorem proper_index_ge_thirteen (q : CFSG.PrimePower) (hq : q.order=3)
    [IsSimpleGroup (CFSG.Models.A 2 q)]
    (H : Subgroup (CFSG.Models.A 2 q)) (hH : H≠⊤) : 13 ≤ H.index :=
  CFSGTypeARankTwoCardTwo.prime_le_proper_index 13 (by decide)
    (thirteen_dvd_projective_card q.Field (q.card_field.trans hq)) H hH

theorem scaled_class_cube_le_proper_index (q : CFSG.PrimePower) (hq : q.order=3)
    [IsSimpleGroup (CFSG.Models.A 2 q)]
    (H : Subgroup (CFSG.Models.A 2 q)) (hH : H≠⊤) :
    25*(Nat.card (ConjClasses (CFSG.Models.A 2 q))*
      Nat.card (Outer (CFSG.Models.A 2 q)))^3 ≤ 3^H.index := by
  have hc : Nat.card (ConjClasses (CFSG.Models.A 2 q)) ≤ 15 := by
    simpa only [hq] using CFSGTypeARankTwoClassCube.class_card_le q
  have hf : q.exponent=1 :=
    (Nat.Prime.pow_inj' q.prime_isPrime (by decide : Nat.Prime 3)
      q.exponent_pos.ne' (by decide : (1:ℕ)≠0)
      (show q.prime^q.exponent=3^1 from hq)).2
  have ho : Nat.card (Outer (CFSG.Models.A 2 q)) ≤ 2 := by
    simpa only [hq,hf] using
      CFSGTypeAOuterGcdCardinality.typeA_higher_outer_card_le_gcd 2 (by decide) q
  exact ((Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left (Nat.mul_le_mul hc ho) 3)).trans
    (by decide +kernel : 25*(15*2)^3 ≤ 3^13)).trans
      (Nat.pow_le_pow_right (by decide) (proper_index_ge_thirteen q hq H hH))

end SymmetricSubgroupAsymptotics.CFSGTypeARankTwoCardThree
