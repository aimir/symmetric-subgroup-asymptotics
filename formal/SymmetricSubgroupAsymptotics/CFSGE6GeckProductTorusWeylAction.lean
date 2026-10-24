import SymmetricSubgroupAsymptotics.CFSGE6GeckProductTorus
import SymmetricSubgroupAsymptotics.CFSGIntegerReflectionPowerHom
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylTorusNormalization
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylWordDegree

/-! Literal Weyl-word conjugation of the actual six-coordinate E6
product torus. Each exponent reflection follows from the checked
matrix torus-generator relation, rather than a torus-recognition premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckProductTorusWeylAction
open CFSGE6GeckProductTorus CFSGIntegerMatrixPowerHom CFSGIntegerReflectionPowerHom
open CFSGNormTwoGeckWeylTorusNormalization CFSGNormTwoGeckWeylWordDegree
open CFSGTwistedE6GeckDiagramCovariance CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoGeckParameterizedTorus CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGSerreQuadraticMatrix CFSGExceptionalNormTwoBases
local notation "A" => CartanMatrix.E₆
variable (K : Type) [Field K]

private theorem simple_pairing (i j : Fin 6) :
    integerPairing A (E6Index j : Roots A).val (E6Index i : Roots A).val=A i j := by
  change integerPairing A (Pi.single j (1:ℤ)) (Pi.single i 1)=A i j
  rw [integerPairing,Matrix.toBilin'_single]
  exact (congrArg (fun M : Matrix (Fin 6) (Fin 6) ℤ=>M j i) CartanMatrix.E₆_transpose).symm

theorem weyl_product_torus (i : Fin 6) (x : Fin 6→Kˣ) :
    canonicalWeyl rawData K i*rawProductTorus K x*(canonicalWeyl rawData K i)⁻¹=
      rawProductTorus K (powerHom (reflectionExponents A i) x) := by
  let F := (MulAut.conj (canonicalWeyl rawData K i)).toMonoidHom.comp (rawProductTorus K)
  let H := (rawProductTorus K).comp (powerHom (reflectionExponents A i))
  change F x=H x
  apply Pi.mulSingle_induction (fun y : Fin 6→Kˣ=>F y=H y) x
  · rw [map_one,map_one]
  · intro y z hy hz
    rw [map_mul,map_mul,hy,hz]
  · intro j t
    change canonicalWeyl rawData K i*rawProductTorus K (Pi.mulSingle j t)*
      (canonicalWeyl rawData K i)⁻¹=
      rawProductTorus K (powerHom (reflectionExponents A i) (Pi.mulSingle j t))
    rw [rawProductTorus_mulSingle,reflection_mulSingle,map_mul,
      rawProductTorus_mulSingle,rawProductTorus_mulSingle]
    have h := weyl_conjugate_torus_generator A CartanMatrix.E₆_transpose E6_positive_definite
      E6Base E6Index K i j t
    rw [simple_pairing] at h
    exact h

def wordReflectionExponents (w : List (Fin 6)) : Matrix (Fin 6) (Fin 6) ℤ :=
  (w.map (reflectionExponents A)).prod

theorem word_product_torus (w : List (Fin 6)) (x : Fin 6→Kˣ) :
    wordUnit A CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K w*
      rawProductTorus K x*
        (wordUnit A CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K w)⁻¹=
      rawProductTorus K (powerHom (wordReflectionExponents w) x) := by
  induction w generalizing x with
  | nil =>
    simp only [wordUnit,wordReflectionExponents,List.map_nil,List.prod_nil,
      one_mul,inv_one,mul_one,powerHom_one]
  | cons i w ih =>
    let W := wordUnit A CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K w
    have hx : W*rawProductTorus K x*W⁻¹=
        rawProductTorus K (powerHom (wordReflectionExponents w) x) := ih x
    change (canonicalWeyl rawData K i*W)*rawProductTorus K x*
      (canonicalWeyl rawData K i*W)⁻¹=
        rawProductTorus K (powerHom (reflectionExponents A i*wordReflectionExponents w) x)
    calc
      _=canonicalWeyl rawData K i*(W*rawProductTorus K x*W⁻¹)*
          (canonicalWeyl rawData K i)⁻¹ := by group
      _=canonicalWeyl rawData K i*rawProductTorus K (powerHom (wordReflectionExponents w) x)*
          (canonicalWeyl rawData K i)⁻¹ := by rw [hx]
      _=rawProductTorus K (powerHom (reflectionExponents A i)
          (powerHom (wordReflectionExponents w) x)) := weyl_product_torus K i _
      _=_ := congrArg (rawProductTorus K) (powerHom_mul _ _ _).symm

end SymmetricSubgroupAsymptotics.CFSGE6GeckProductTorusWeylAction
