import SymmetricSubgroupAsymptotics.FiniteHermitianUnitPerp
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! A unit vector removes exactly one dimension inside the SAME subspace.
The dimension statement follows from the literal pairing functional,
whose surjectivity is witnessed by scalar multiples of that vector. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteHermitianUnitPerpDimension
open CFSGTwistedAUnitaryParameters CFSGHermitianOrthogonalSpan
open FiniteHermitianUnitPerp

theorem finrank_add_one {K I : Type*} [Field K] [Fintype I]
    (sigma : K ≃+* K) (H : Matrix I I K)
    (W : Submodule K (I → K)) (v : I → K)
    (hv : v ∈ W) (hone : hermitianPair sigma H v v=1) :
    Module.finrank K (unitPerp sigma H W v)+1=Module.finrank K W := by
  let f : W →ₗ[K] K := (pairRightLinear sigma H v).comp W.subtype
  have hsurj : Function.Surjective f := by
    intro a
    refine ⟨⟨a • v,W.smul_mem a hv⟩,?_⟩
    change hermitianPair sigma H v (a • v)=a
    have hh := hermitianPair_smul sigma H 1 a v v
    simpa only [one_smul,map_one,one_mul,hone,mul_one] using hh
  have hmap : f.ker.map W.subtype=unitPerp sigma H W v := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨y.property,hy⟩
    · intro hx
      exact ⟨⟨x,hx.1⟩,hx.2,rfl⟩
  have hd : Module.finrank K f.ker=Module.finrank K (unitPerp sigma H W v) := by
    rw [←hmap]
    exact (Submodule.equivMapOfInjective W.subtype W.subtype_injective f.ker).finrank_eq
  have hr : f.range=⊤ := LinearMap.range_eq_top.mpr hsurj
  have hh := f.finrank_range_add_finrank_ker
  rw [hr,finrank_top,Module.finrank_self,hd] at hh
  omega

end SymmetricSubgroupAsymptotics.FiniteHermitianUnitPerpDimension
