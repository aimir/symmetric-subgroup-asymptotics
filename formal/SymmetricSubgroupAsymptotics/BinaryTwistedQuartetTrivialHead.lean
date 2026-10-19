import SymmetricSubgroupAsymptotics.BinaryTwistedQuartetLoewyCoordinates
import SymmetricSubgroupAsymptotics.BinaryPlaneFunctions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Every actual cycle-trivial quotient of every invariant binary
subspace has dimension at most TWO. This supplies the retained binary
axis (top order at most two) without a false whole-socle-two assertion. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryTwistedQuartetTrivialHead
open BinaryTwistedQuartetPolynomial (Bit Plane cubic)
open BinaryTwistedQuartetLoewyCoordinates

private theorem cubic_cube : ∀ u : Plane, cubic (cubic (cubic u))=u := by decide +kernel
private theorem cubic_fixed_zero : ∀ u : Plane, cubic u=u → u=0 := by decide +kernel
private theorem add_self {Q : Type} [AddCommGroup Q] [Module Bit Q] (x : Q) : x+x=0 := by
  rw [← two_smul Bit,show (2 : Bit)=0 by decide,zero_smul]

def cycleEnd : Module.End Bit Space where
  toFun := cycleAction
  map_add' u v := by
    funext i j
    fin_cases i <;> fin_cases j <;> simp [cycleAction,cubic] <;> ring
  map_smul' a v := by
    funext i j
    fin_cases i <;> fin_cases j <;> simp [cycleAction,cubic,mul_add]

theorem cycle_cube (v : Space) : cycleEnd (cycleEnd (cycleEnd v))=v := by
  change cycleAction (cycleAction (cycleAction v))=v
  funext i
  fin_cases i <;> simp [cycleAction,cubic_cube]

private theorem fixed_eq_of_eval (v w : Space)
    (hv : cycleEnd v=v) (hw : cycleEnd w=w) (h : v 1=w 1) : v=w := by
  have hv0 : v 0=0 := cubic_fixed_zero (v 0)
    (congrArg (fun z : Space => z 0) hv)
  have hw0 : w 0=0 := cubic_fixed_zero (w 0)
    (congrArg (fun z : Space => z 0) hw)
  have hv2 : cubic (v 1)=v 2 := congrArg (fun z : Space => z 2) hv
  have hw2 : cubic (w 1)=w 2 := congrArg (fun z : Space => z 2) hw
  have hv3 : cubic (v 2)=v 3 := congrArg (fun z : Space => z 3) hv
  have hw3 : cubic (w 2)=w 3 := congrArg (fun z : Space => z 3) hw
  have h2 : v 2=w 2 := hv2.symm.trans ((congrArg cubic h).trans hw2)
  funext i
  fin_cases i
  · exact hv0.trans hw0.symm
  · exact h
  · exact h2
  · exact hv3.symm.trans ((congrArg cubic h2).trans hw3)

theorem rank_le_two (W : Submodule Bit Space)
    (hcycle : ∀ v, v∈W → cycleAction v∈W)
    {Q : Type} [AddCommGroup Q] [Module Bit Q]
    (q : W →ₗ[Bit] Q) (hq : Function.Surjective q)
    (htrivial : ∀ v : W, q ⟨cycleAction v,hcycle v v.property⟩=q v) :
    Module.finrank Bit Q≤2 := by
  let e : W →ₗ[Bit] Space := W.subtype+
    cycleEnd.comp W.subtype+(cycleEnd^2).comp W.subtype
  have hef : ∀ v : W, cycleEnd (e v)=e v := by
    intro v
    change cycleEnd (v.val+cycleEnd v.val+cycleEnd (cycleEnd v.val))=
      v.val+cycleEnd v.val+cycleEnd (cycleEnd v.val)
    rw [map_add,map_add,cycle_cube]
    abel
  let ev : e.range →ₗ[Bit] Plane := (LinearMap.proj 1).comp e.range.subtype
  have hev : Function.Injective ev := by
    intro v w h
    apply Subtype.ext
    obtain ⟨a,ha⟩ := v.property
    obtain ⟨b,hb⟩ := w.property
    have hvf : cycleEnd v.val=v.val := ha ▸ hef a
    have hwf : cycleEnd w.val=w.val := hb ▸ hef b
    exact fixed_eq_of_eval v.val w.val hvf hwf h
  have her : Module.finrank Bit e.range≤2 :=
    (ev.finrank_le_finrank_of_injective hev).trans (by simp [Plane])
  have hk : e.ker≤q.ker := by
    intro v hv
    let va : W := ⟨cycleAction v,hcycle v v.property⟩
    let vb : W := ⟨cycleAction va,hcycle va va.property⟩
    let z := v+va+vb
    have hqz : q z=q v := by
      change q (v+va+vb)=q v
      rw [map_add,map_add,htrivial,htrivial,htrivial]
      rw [add_self,zero_add]
    have hz : z=0 := Subtype.ext hv
    rw [hz,map_zero] at hqz
    exact hqz.symm
  have hker := Submodule.finrank_mono hk
  have he := e.finrank_range_add_finrank_ker
  have hqr := q.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hq,finrank_top] at hqr
  omega

end SymmetricSubgroupAsymptotics.BinaryTwistedQuartetTrivialHead
