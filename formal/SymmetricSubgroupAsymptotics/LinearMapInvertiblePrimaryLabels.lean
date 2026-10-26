import SymmetricSubgroupAsymptotics.LinearMapPositivePrimaryDecomposition
import SymmetricSubgroupAsymptotics.LinearMapCyclicConstantCoefficient
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-! Actual primary labels of an invertible operator have nonzero
constant coefficient and degree at most the SAME original dimension.
These restrictions are read from its proved primary quotient chart;
no canonical-form uniqueness or class-number premise is supplied. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.LinearMapInvertiblePrimaryLabels
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]

theorem prime_constantCoeff_ne_zero (g : LinearMap.GeneralLinearGroup K V)
    (C : LinearMapPositivePrimaryDecomposition.Chart (g : Module.End K V))
    (i : C.cyclic.ι) : (C.prime i).coeff 0≠0 := by
  intro hz
  have hc := LinearMapCyclicConstantCoefficient.constantCoeff_ne_zero C.cyclic
    g.toLinearEquiv.surjective i
  rw [C.power_eq i] at hc
  have he : ((C.prime i)^C.exponent i).coeff 0=((C.prime i).coeff 0)^C.exponent i :=
    Polynomial.constantCoeff.map_pow _ _
  rw [he,hz,zero_pow (C.positive i).ne'] at hc
  exact hc rfl

theorem prime_natDegree_le_finrank (g : LinearMap.GeneralLinearGroup K V)
    (C : LinearMapPositivePrimaryDecomposition.Chart (g : Module.End K V))
    (i : C.cyclic.ι) : (C.prime i).natDegree ≤ Module.finrank K V := by
  have hi : C.exponent i*(C.prime i).natDegree ≤
      ∑ j : C.cyclic.ι, C.exponent j*(C.prime j).natDegree :=
    Finset.single_le_sum (s := Finset.univ)
      (f := fun j : C.cyclic.ι => C.exponent j*(C.prime j).natDegree)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hlo : (C.prime i).natDegree ≤ C.exponent i*(C.prime i).natDegree :=
    Nat.le_mul_of_pos_left _ (C.positive i)
  exact (hlo.trans hi).trans_eq C.degree_sum

end SymmetricSubgroupAsymptotics.LinearMapInvertiblePrimaryLabels
