import SymmetricSubgroupAsymptotics.BinaryTwistedQuartetMiddleKernel
import SymmetricSubgroupAsymptotics.BinaryPlaneFunctions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The nontrivial cubic part of an actual quotient of a radical
submodule has binary dimension at most TWO once its constant layer is
killed. This is a relative-head statement, not a supplied capacity. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryTwistedQuartetRadicalHead
open BinaryTwistedQuartetPolynomial (Bit Plane cubic)
open BinaryTwistedQuartetLoewyCoordinates

def middleLinear : Space →ₗ[Bit] Plane × Plane where
  toFun := middle
  map_add' u v := by
    apply Prod.ext <;> ext i <;> fin_cases i <;>
      simp [middle,cubic,Matrix.vecHead,Matrix.vecTail] <;> ring
  map_smul' a v := by
    apply Prod.ext <;> ext i <;> fin_cases i <;>
      simp [middle,cubic,Matrix.vecHead,Matrix.vecTail] <;> ring

def sumLinear : Space →ₗ[Bit] Plane where
  toFun := sumBlocks
  map_add' u v := by ext i; simp [sumBlocks]; abel
  map_smul' a v := by ext i; simp [sumBlocks,mul_add]

private theorem add_self {Q : Type} [AddCommGroup Q] [Module Bit Q] (x : Q) : x+x=0 := by
  rw [← two_smul Bit,show (2 : Bit)=0 by decide,zero_smul]

theorem nontrivial_rank_le_two (W : Submodule Bit Space)
    (hcycle : ∀ v, v∈W → cycleAction v∈W)
    (hrad : ∀ v, v∈W → sumBlocks v=0)
    {Q : Type} [AddCommGroup Q] [Module Bit Q]
    (q : W →ₗ[Bit] Q) (hq : Function.Surjective q) (T : Module.End Bit Q)
    (hinter : ∀ v : W, q ⟨cycleAction v,hcycle v v.property⟩=T (q v))
    (hconstant : ∀ v : W, (v : Space)=constant (v.val 0) → q v=0) :
    Module.finrank Bit (LinearMap.range (T+T^2))≤2 := by
  let beta : W →ₗ[Bit] Plane :=
    (LinearMap.snd Bit Plane Plane).comp (middleLinear.comp W.subtype)
  let f := (T+T^2).comp q
  have hker : beta.ker≤f.ker := by
    intro v hv
    have hb : (middle v.val).2=0 := hv
    let w : W := ⟨cycleAction v.val+v.val,W.add_mem (hcycle v v.property) v.property⟩
    have hwr : sumBlocks w.val=0 := by
      change sumLinear (cycleAction v.val+v.val)=0
      rw [map_add]
      change sumBlocks (cycleAction v.val)+sumBlocks v.val=0
      rw [sum_cycle,hrad v v.property]
      simp [cubic]
    have hwm : middle w.val=0 := by
      change middleLinear (cycleAction v.val+v.val)=0
      rw [map_add]
      change middle (cycleAction v.val)+middle v.val=0
      rw [middle_cycle_on_radical v.val (hrad v v.property)]
      apply Prod.ext
      · exact binaryVector_add_self _
      · simp [hb,cubic]
    have hwzero : q w=0 := hconstant w
      (BinaryTwistedQuartetMiddleKernel.eq_constant w.val hwr hwm)
    have hsum : T (q v)+q v=0 := by
      have hw : w=⟨cycleAction v.val,hcycle v v.property⟩+v := rfl
      rw [hw,map_add,hinter] at hwzero
      exact hwzero
    have hfix : T (q v)=q v := add_right_cancel (hsum.trans (add_self (q v)).symm)
    change (T+T^2) (q v)=0
    change T (q v)+T (T (q v))=0
    simp only [hfix]
    exact add_self _
  have hk := Submodule.finrank_mono hker
  have hb := beta.finrank_range_add_finrank_ker
  have hf := f.finrank_range_add_finrank_ker
  have hr : Module.finrank Bit beta.range≤2 := by
    exact beta.range.finrank_le.trans (by simp [Plane])
  have hfr : Module.finrank Bit f.range≤2 := by omega
  have he : f.range=(T+T^2).range := by
    ext x
    constructor
    · rintro ⟨v,rfl⟩
      exact ⟨q v,rfl⟩
    · rintro ⟨v,rfl⟩
      obtain ⟨w,rfl⟩ := hq v
      exact ⟨w,rfl⟩
  rw [← he]
  exact hfr

end SymmetricSubgroupAsymptotics.BinaryTwistedQuartetRadicalHead
