import SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalIntrinsicEquivalence
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! The literal original D Cartan/root vectors are an integral basis.
Its scalar-extension basis is the SAME original tensor Space, including
characteristic two. This does not assert ambient matrix faithfulness. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalIntegralBasis
open CFSG.Models.Chevalley CFSGOrthogonalDOriginalRootCandidates
open CFSGOrthogonalDOriginalIntrinsicEquivalence
variable (r : ℕ) (hr : 4 ≤ r)
local instance : DecidableEq (BasisIndex r):=Classical.decEq _

def coefficientMap : Source r→ₗ[ℤ](BasisIndex r→ℤ) :=
  (CFSGOrthogonalDIntrinsicPrimitiveCoordinates.coordinates r hr).comp
    (CFSGOrthogonalDOriginalIntrinsicImage.realization r hr)

theorem coefficientMap_vector (j : BasisIndex r) :
    coefficientMap r hr (vector r hr j)=Pi.single j 1 := primitive_coordinates r hr j

def coefficientEquiv : Source r≃ₗ[ℤ](BasisIndex r→ℤ) :=
  LinearEquiv.ofLinear (coefficientMap r hr) (Fintype.linearCombination ℤ (vector r hr))
    (by
      apply LinearMap.ext
      intro a
      exact FiniteIntegralFamilySplitRealization.coordinates_combination
        (CFSGOrthogonalDOriginalIntrinsicImage.realization r hr) (vector r hr)
        (CFSGOrthogonalDIntrinsicPrimitiveCoordinates.coordinates r hr)
        (primitive_coordinates r hr) a)
    (by apply LinearMap.ext;intro x;exact reconstruction r hr x)

def basis : Module.Basis (BasisIndex r) ℤ (Source r) :=
  Module.Basis.ofEquivFun (coefficientEquiv r hr)

theorem basis_apply (j : BasisIndex r) : basis r hr j=vector r hr j := by
  rw [basis,Module.Basis.coe_ofEquivFun]
  apply (coefficientEquiv r hr).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (coefficientMap_vector r hr j).symm

def tensorBasis (K : Type) [Field K] :
    Module.Basis (BasisIndex r) K (Space (CartanMatrix.D r) K) :=
  (basis r hr).baseChange K

theorem tensorBasis_apply (K : Type) [Field K] (j : BasisIndex r) :
    tensorBasis r hr K j=(1 : K) ⊗ₜ[ℤ] vector r hr j := by
  rw [tensorBasis,Module.Basis.baseChange_apply,basis_apply]

theorem tensor_expansion (K : Type) [Field K] (x : Space (CartanMatrix.D r) K) :
    ∑ j : BasisIndex r,(tensorBasis r hr K).repr x j • ((1 : K) ⊗ₜ[ℤ] vector r hr j)=x := by
  simpa only [←tensorBasis_apply r hr K] using (tensorBasis r hr K).sum_repr x

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalIntegralBasis
