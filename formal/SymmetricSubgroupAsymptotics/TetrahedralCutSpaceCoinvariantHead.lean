import SymmetricSubgroupAsymptotics.BinaryBitmaskCoordinates
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Field.ZMod

/-! The tetrahedral cut module in its three star coordinates. Killing
its actual Klein differences leaves a one-dimensional cubic-fixed head.
The quotient map is arbitrary and surjective, not chosen by a census. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TetrahedralCutSpaceCoinvariantHead
abbrev Bit := ZMod 2
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
abbrev Vector := Fin 3 → Bit

def A : Module.End Bit Vector :=
  (show Matrix (Fin 3) (Fin 3) Bit from ![![0,0,1],![1,0,0],![0,1,0]]).mulVecLin
def B : Module.End Bit Vector :=
  (show Matrix (Fin 3) (Fin 3) Bit from ![![0,1,1],![0,1,0],![1,1,0]]).mulVecLin
def D0 : Module.End Bit Vector := 1+B
def D1 : Module.End Bit Vector := A*D0*A^2
def delta : Vector := ![1,0,0]

private theorem decomposition : ∀ v : Vector,
    v=(v 0+v 1+v 2) • delta+
      D0 (Pi.single 0 (v 2))+D1 (Pi.single 0 (v 1)) := by decide +kernel
private theorem active_decomposition : ∀ v : Vector,
    (A+A^2) v=D0 (Pi.single 0 (v 0+v 1))+
      D1 (Pi.single 0 (v 0+v 2)) := by decide +kernel

variable {Q : Type} [AddCommGroup Q] [Module Bit Q] [FiniteDimensional Bit Q]
    (q : Vector →ₗ[Bit] Q) (hq : Function.Surjective q)
    (hD0 : ∀ v,q (D0 v)=0) (hD1 : ∀ v,q (D1 v)=0)

include hq hD0 hD1 in
theorem finrank_le_one : Module.finrank Bit Q ≤ 1 := by
  have span (v : Vector) : q v=(v 0+v 1+v 2) • q delta := by
    have h := congrArg q (decomposition v)
    simpa only [map_add,map_smul,hD0,hD1,add_zero] using h
  let f : Bit →ₗ[Bit] Q :=
    { toFun := fun r => r • q delta
      map_add' := fun r s => add_smul r s (q delta)
      map_smul' := fun r s => mul_smul r s (q delta) }
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨v,rfl⟩ := hq y
    exact ⟨v 0+v 1+v 2,(span v).symm⟩
  have h := f.finrank_le_finrank_of_surjective hf
  simpa using h

include hq hD0 hD1 in
theorem projector_heads (T : Module.End Bit Q) (hA : ∀ v,q (A v)=T (q v)) :
    Module.finrank Bit (LinearMap.range (1+T+T^2)) ≤ 1 ∧
    Module.finrank Bit (LinearMap.range (T+T^2)) ≤ 0 := by
  have hzero (v : Vector) : q ((A+A^2) v)=0 := by
    rw [active_decomposition,map_add,hD0,hD1,zero_add]
  have he : T+T^2=0 := by
    apply LinearMap.ext
    intro y
    obtain ⟨v,rfl⟩ := hq y
    have h : q ((A+A^2) v)=(T+T^2) (q v) := by
      simp only [LinearMap.add_apply,map_add,pow_two,Module.End.mul_apply,hA]
    exact h.symm.trans (hzero v)
  refine ⟨(Submodule.finrank_le _).trans (finrank_le_one q hq hD0 hD1),?_⟩
  rw [he,LinearMap.range_zero]
  simp
end SymmetricSubgroupAsymptotics.TetrahedralCutSpaceCoinvariantHead
