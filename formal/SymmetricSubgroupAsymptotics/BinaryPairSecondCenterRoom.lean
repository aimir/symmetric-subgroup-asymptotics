import SymmetricSubgroupAsymptotics.BinaryPairSecondCenterKernel
import SymmetricSubgroupAsymptotics.BinaryConstantDisplacementDimension
import Mathlib.Algebra.Module.ZMod

/-! The SAME original second centre has constant-displacement kernel
bits. For a large kernel it lies wholly in that kernel, so a genuine
nonelementary actual16point top bounds its order by sixteen. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance secondCenterRoomPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w)) [MulAction.IsPretransitive U X]
include F

theorem second_center_axis_constant_displacements
    (g : F.top.range) (v : F.ambientAxis (Subgroup.upperCentralSeries U 2))
    (x y : Fin w) : v.val (g • x)-v.val x=v.val (g • y)-v.val y := by
  letI : MulAction.IsPretransitive F.top.range (Fin w) := F.top_pretransitive
  obtain ⟨k,hk,hbits⟩ := (F.mem_ambientAxis (Subgroup.upperCentralSeries U 2) v.val).mp v.property
  obtain ⟨u,hu⟩ := F.top.rangeRestrict_surjective g⁻¹
  let c : F.top.ker := k⁻¹*MulAut.conjNormal u k
  have hc : (c : U)∈Subgroup.center U := by
    have he : (c : U)=⁅(k : U)⁻¹,u⁆ := by rfl
    rw [he]
    have hh := Subgroup.mem_upperCentralSeries_succ_iff.mp
      ((Subgroup.upperCentralSeries U 2).inv_mem hk) u
    simpa only [Subgroup.upperCentralSeries_one] using hh
  have hd : F.coordinateTopAction g⁻¹ v.val-v.val=F.bits c := by
    rw [←hu,←hbits]
    exact (F.bits_commutator u k).symm
  have he (i : Fin w) : (F.coordinateTopAction g⁻¹ v.val-v.val) i=
      v.val (g • i)-v.val i := by
    change v.val ((g.val⁻¹)⁻¹ i)-v.val i=v.val (g • i)-v.val i
    rw [inv_inv]
    rfl
  have hx := congrFun hd x
  have hy := congrFun hd y
  rw [he] at hx hy
  exact hx.trans ((F.central_kernel_bits_constant c hc x y).trans hy.symm)

end SymmetricSubgroupAsymptotics.BinaryPairFrame

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance secondCenterRoomCardPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16)) [MulAction.IsPretransitive U X]
include F

theorem original_second_center_card_le_sixteen_of_large_nonelementary_kernel
    (hU : IsPGroup 2 U) (hlarge : 10≤Module.finrank (ZMod 2) F.kernelSpace)
    (hnon : ¬BinarySquareActionStructure.SquaresActTrivially (G := F.top.range) (X := Fin 16)) :
    Nat.card (Subgroup.upperCentralSeries U 2)≤16 := by
  letI : MulAction.IsPretransitive F.top.range (Fin 16) := F.top_pretransitive
  let W := F.ambientAxis (Subgroup.upperCentralSeries U 2)
  have hd : Module.finrank (ZMod 2) W≤4 :=
    BinaryConstantDisplacementDimension.finrank_le_four_of_not_squares_trivial
      W (0 : Fin 16) (by simp only [Nat.card_fin])
      (fun g v x y => F.second_center_axis_constant_displacements g v x y) hnon
  have hWcard : Nat.card W≤16 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2)]
    simpa only [Nat.card_zmod] using
      (Nat.pow_le_pow_right (by decide : 0<(2 : ℕ)) hd)
  have hker : Subgroup.upperCentralSeries U 2≤F.top.ker :=
    F.original_second_center_le_kernel_of_large_kernel hU (0 : Fin 16) (by omega)
  let f : Subgroup.upperCentralSeries U 2 → W := fun z =>
    ⟨F.bits ⟨z.val,hker z.property⟩,
      (F.bits_mem_ambientAxis (Subgroup.upperCentralSeries U 2) ⟨z.val,hker z.property⟩).mpr z.property⟩
  have hf : Function.Injective f := by
    intro a b he
    have hb := congrArg (fun z : W => z.val) he
    change F.bits (⟨a.val,hker a.property⟩ : F.top.ker)=
      F.bits (⟨b.val,hker b.property⟩ : F.top.ker) at hb
    have hk := F.bitsHom_injective (congrArg Multiplicative.ofAdd hb)
    exact Subtype.ext (congrArg (fun k : F.top.ker => (k : U)) hk)
  exact (Nat.card_le_card_of_injective f hf).trans hWcard
end SymmetricSubgroupAsymptotics.BinaryPairFrame
