import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-! The canonical cyclic polynomial module has its actual defining
monic polynomial as characteristic polynomial. This also transfers
along an actual intertwining linear equivalence, providing the cyclic
summand link needed for a PID conjugacy code. No irreducibility,
classification, or finite-field hypothesis is required. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PolynomialCyclicCharacteristicPolynomial
open Polynomial
variable {K : Type*} [Field K]

def cyclicMatrix (p : K[X]) (hp : p.Monic) :
    Matrix (Fin p.natDegree) (Fin p.natDegree) K :=
  Algebra.leftMulMatrix (AdjoinRoot.powerBasis hp.ne_zero).basis (AdjoinRoot.root p)

theorem cyclicMatrix_charpoly (p : K[X]) (hp : p.Monic) :
    (cyclicMatrix p hp).charpoly = p := by
  exact (charpoly_leftMulMatrix (AdjoinRoot.powerBasis hp.ne_zero)).trans
    (AdjoinRoot.minpoly_powerBasis_gen_of_monic hp)

def rootOperator (p : K[X]) : Module.End K (AdjoinRoot p) :=
  LinearMap.mulLeft K (AdjoinRoot.root p)

theorem rootOperator_apply (p : K[X]) (x : AdjoinRoot p) :
    rootOperator p x = AdjoinRoot.root p * x := rfl

theorem rootOperator_charpoly (p : K[X]) (hp : p.Monic) :
    letI : Module.Finite K (AdjoinRoot p) := hp.finite_adjoinRoot
    (rootOperator p).charpoly = p := by
  letI : Module.Finite K (AdjoinRoot p) := hp.finite_adjoinRoot
  rw [← LinearMap.charpoly_toMatrix (rootOperator p)
    (AdjoinRoot.powerBasis hp.ne_zero).basis]
  exact cyclicMatrix_charpoly p hp

theorem charpoly_eq_of_intertwining
    {V : Type*} [AddCommGroup V] [Module K V] [Module.Finite K V]
    (A : Module.End K V) (p : K[X]) (hp : p.Monic)
    (e : V ≃ₗ[K] AdjoinRoot p)
    (he : ∀ v : V, e (A v) = AdjoinRoot.root p * e v) : A.charpoly = p := by
  letI : Module.Finite K (AdjoinRoot p) := hp.finite_adjoinRoot
  have hc : e.conj A = rootOperator p := by
    apply LinearMap.ext
    intro x
    change e (A (e.symm x)) = AdjoinRoot.root p * x
    rw [he, e.apply_symm_apply]
  rw [← e.charpoly_conj A, hc]
  exact rootOperator_charpoly p hp

end SymmetricSubgroupAsymptotics.PolynomialCyclicCharacteristicPolynomial
