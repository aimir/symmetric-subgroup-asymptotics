import SymmetricSubgroupAsymptotics.PrimitiveAffineTernaryTwentySevenClassBound
import SymmetricSubgroupAsymptotics.PrimitiveTopSmallFibreClassBudget

/-! Original binary/ternary fibres with the actual primitive affine
ternary27 top. The original subnormal subgroup, block map and primitive
premise are retained; the class budget comes from the SAME elementary
module and parabolic recursion, not a supplied capacity or action row. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineTernaryTopSmallFibreClassBound
open OriginalBlockClassBound

theorem binary_unsigned_capacity :
    (((12247:ℕ)+1)*2^(27-2))^3≤5^(2*27-1) := by decide +kernel

theorem ternary_capacity : (3^27*(12247:ℕ))^3≤5^(3*27-1) := by decide +kernel

theorem affine_order_lt_factorial : (27:ℕ)*27^Nat.log 2 27<(27:ℕ).factorial := by decide +kernel

theorem subnormal_class_cube_le_at_original_degree
    {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (P : PrimitiveAffineProfile (Top (A:=A) (X:=X)) X)
    (hprimitive : MulAction.IsPreprimitive (Top (A:=A) (X:=X)) X)
    (hdegree : Nat.card X=27) (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card Ω-1) := by
  letI : Nonempty X := Finite.card_pos_iff.mp (by omega)
  let x₀ : X := Classical.arbitrary X
  have htop : ∀ L : Subgroup (Top (A:=A) (X:=X)), L.IsSubnormal →
      Nat.card (ConjClasses L)≤12247 :=
    fun L _ => PrimitiveAffineTernaryTwentySevenClassBound.subgroup_class_card_le_twelveTwoFortySeven
      P hprimitive x₀ hdegree L
  have horder : Nat.card (Top (A:=A) (X:=X))<(Nat.card X).factorial :=
    (P.card_le_domain_pow_log x₀).trans_lt (by
      simpa only [hdegree] using affine_order_lt_factorial)
  exact PrimitiveTopSmallFibreClassBudget.subnormal_class_cube_le_at_original_degree
    π hπ c hc hsize (by omega) hprimitive horder 12247 (by decide) htop
    (by simpa only [hdegree] using binary_unsigned_capacity)
    (by simpa only [hdegree] using ternary_capacity) H hH

end SymmetricSubgroupAsymptotics.PrimitiveAffineTernaryTopSmallFibreClassBound
