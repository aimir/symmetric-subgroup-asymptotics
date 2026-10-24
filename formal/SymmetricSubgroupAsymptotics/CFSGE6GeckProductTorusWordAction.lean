import SymmetricSubgroupAsymptotics.CFSGE6GeckProductTorusRootAction
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWordTorusScaling

/-! The same genuine E6 product torus scales an actual displayed
Weyl-word root chart. The proved single-torus word identity is assembled
by the common product-action theorem; its integral sign has already
cancelled in that identity. No root or Weyl census is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckProductTorusWordAction
open CFSGE6GeckProductTorus CFSGE6GeckProductTorusRootAction
open CFSGTwistedE6GeckDiagramCovariance CFSGE6GeckSignedSimpleParameters
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoCoordinateWordTorusScaling CFSGNormTwoGeckTorusHom
open CFSGNormTwoGeckParameterizedTorus CFSGNormTwoGeckWeylWordDegree
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord CFSGSerreQuadraticWordRootTransport
open CFSGNormTwoRootPairing CFSGIntegerMatrixPairing CFSGProductTorusAction
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
local instance : DecidableEq (Roots A) := Classical.decEq _

private def wordParameterHom (K : Type) [Field K] (w : List (Fin 6)) (j : Fin 6) :
    Multiplicative K →* (Matrix GeckIndex GeckIndex K)ˣ :=
  (MulAut.conj (canonicalWord rawData K w)).toMonoidHom.comp (rawSimpleHom K false j)

theorem product_torus_positive_word_action (K : Type) [Field K]
    (x : Fin 6 → Kˣ) (w : List (Fin 6)) (j : Fin 6) (a : K) :
    rawProductTorus K x*rootWord rawData K w false j a*(rawProductTorus K x)⁻¹=
      rootWord rawData K w false j
        (a*(rootCharacter K x (wordRoot A hs hp E6Base E6Index w (E6Index j)) : K)) := by
  let B : Matrix (Fin 6) (Fin 6) ℤ := fun _ i=>integerPairing A (E6Index i : Roots A).val
    (wordRoot A hs hp E6Base E6Index w (E6Index j)).val
  have hact (i : Fin 6) (t : Kˣ) (_ : Fin 6) (b : K) :
      simpleTorusHom K i t*wordParameterHom K w j (Multiplicative.ofAdd b)*
        (simpleTorusHom K i t)⁻¹=
      wordParameterHom K w j (Multiplicative.ofAdd (b*(t : K)^B 0 i)) := by
    change parameterTorusHom A hs hp E6Base E6Index K i t*rootWord rawData K w false j b*
      (parameterTorusHom A hs hp E6Base E6Index K i t)⁻¹=_
    rw [parameterTorusHom_apply]
    exact torus_conjugate_positive_word A hd hs hp ho K i t w j b
  exact product_action (simpleTorusHom K) (simple_tori_commute K) B
    (fun _=>wordParameterHom K w j) hact x 0 a

end SymmetricSubgroupAsymptotics.CFSGE6GeckProductTorusWordAction
