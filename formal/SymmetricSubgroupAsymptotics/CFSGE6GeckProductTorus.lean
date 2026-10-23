import SymmetricSubgroupAsymptotics.CFSGE6GeckRelativeScalarCoordinates
import SymmetricSubgroupAsymptotics.CFSGE6GeckPairedParameterizedWeyl
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckTorusHom
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckTorusConjugation
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckBorelEnvelope
import SymmetricSubgroupAsymptotics.CFSGProductTorusAction

/-! The literal product of the six E6 rank-one tori, with its exact
Cartan scaling action and its four-orbit decomposition on compatible
field-diagram tuples. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckProductTorus
open CFSGTwistedE6GeckDiagramCovariance CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGNormTwoGeckTorusHom
open CFSGNormTwoGeckParameterizedTorus CFSGNormTwoGeckDiagonalTorus
open CFSGNormTwoGeckTorusConjugation CFSGNormTwoGeckBorelEnvelope
open CFSGProductTorusAction CFSGIntegerMatrixPowerHom CFSGIntegerMatrixPairing
open CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix CFSGNormTwoGeckIntegralRealization
open CFSGE6GeckRelativeScalarTuples CFSGE6GeckRelativeScalarCoordinates
open CFSGE6GeckSignedSimpleParameters CFSGE6GeckPairedParameterizedWeyl
open CFSGTwistedE6PairedFixedRoots CFSGTwistedE6FixedA2

variable (K : Type) [Field K]

def simpleTorusHom (i : Fin 6) : Kˣ→*(Matrix GeckIndex GeckIndex K)ˣ :=
  parameterTorusHom CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
    E6Base E6Index K i

theorem simple_tori_commute : Pairwise fun i j => ∀t u,
    Commute (simpleTorusHom K i t) (simpleTorusHom K j u) := by
  intro i j _ t u
  change _*_=_*_
  apply Units.ext
  simp only [Units.val_mul,simpleTorusHom,parameterTorusHom_apply,
    torus_diagonal,Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  exact mul_comm _ _

def rawProductTorus : (Fin 6→Kˣ)→*(Matrix GeckIndex GeckIndex K)ˣ :=
  productTorusHom (simpleTorusHom K) (simple_tori_commute K)

@[simp] theorem rawProductTorus_mulSingle (i : Fin 6) (t : Kˣ) :
    rawProductTorus K (Pi.mulSingle i t)=
      parameterTorus CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
        E6Base E6Index K i t := by
  exact (MonoidHom.noncommPiCoprod_mulSingle (hcomm := simple_tori_commute K)
    (simpleTorusHom K) i t).trans
    (parameterTorusHom_apply _ _ _ _ _ K i t)

theorem rawProductTorus_mem_torus (x : Fin 6→Kˣ) :
    rawProductTorus K x∈torusGroup CartanMatrix.E₆ CartanMatrix.E₆_transpose
      E6_positive_definite E6Base E6Index K := by
  let T := torusGroup CartanMatrix.E₆ CartanMatrix.E₆_transpose
    E6_positive_definite E6Base E6Index K
  apply Pi.mulSingle_induction (fun y : Fin 6→Kˣ => rawProductTorus K y∈T) x
  · rw [map_one]; exact T.one_mem
  · intro y z hy hz
    rw [map_mul]
    exact T.mul_mem hy hz
  · intro i t
    rw [rawProductTorus_mulSingle]
    exact Subgroup.subset_closure ⟨(i,t),rfl⟩

theorem rawProductTorus_simple_action (x : Fin 6→Kˣ) (j : Fin 6) (a : K) :
    rawProductTorus K x*canonicalRoot rawData K false j a*(rawProductTorus K x)⁻¹=
      canonicalRoot rawData K false j (a*(powerHom (G := Kˣ) CartanMatrix.E₆ x j : K)) := by
  apply product_action (simpleTorusHom K) (simple_tori_commute K) CartanMatrix.E₆
    (rawSimpleHom K false) ?_ x j a
  intro i t k b
  have hp : integerPairing CartanMatrix.E₆ (E6Index i : Roots CartanMatrix.E₆).val
      (E6Index k : Roots CartanMatrix.E₆).val=CartanMatrix.E₆ k i := by
    change integerPairing CartanMatrix.E₆ (Pi.single i 1) (Pi.single k 1)=CartanMatrix.E₆ k i
    simp only [integerPairing,Matrix.toBilin'_single]
    exact (congrArg (fun M : Matrix (Fin 6) (Fin 6) ℤ => M i k) CartanMatrix.E₆_transpose).symm
  change parameterTorusHom CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
      E6Base E6Index K i t*canonicalRoot rawData K false k b*
    (parameterTorusHom CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
      E6Base E6Index K i t)⁻¹=_
  rw [parameterTorusHom_apply]
  simpa only [hp] using torus_conjugate_positive CartanMatrix.E₆ CartanMatrix.E₆_transpose
    E6_positive_definite E6Base E6Index K i k t b

theorem rawProductTorus_orbit_factors (sigma : RingAut K) (x : relativeScalars K sigma) :
    rawProductTorus K x.val=pairedParameterTorus K sigma 0 (x.val 0)*
      (pairedParameterTorus K sigma 1 (x.val 2)*
        (parameterTorus CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
            E6Base E6Index K 1 (x.val 1)*
          parameterTorus CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
            E6Base E6Index K 3 (x.val 3))) := by
  calc
    rawProductTorus K x.val=rawProductTorus K
        ((Pi.mulSingle 0 (x.val 0)*Pi.mulSingle 5 (scalarTwist K sigma (x.val 0)))*
          ((Pi.mulSingle 2 (x.val 2)*Pi.mulSingle 4 (scalarTwist K sigma (x.val 2)))*
            (Pi.mulSingle 1 (x.val 1)*Pi.mulSingle 3 (x.val 3)))) :=
      congrArg (rawProductTorus K) (scalar_tuple_decomposition K sigma x)
    _=_ := by
      simp only [map_mul,rawProductTorus_mulSingle]
      rw [pairedParameterTorus_eq,pairedParameterTorus_eq]
      rfl

end SymmetricSubgroupAsymptotics.CFSGE6GeckProductTorus
