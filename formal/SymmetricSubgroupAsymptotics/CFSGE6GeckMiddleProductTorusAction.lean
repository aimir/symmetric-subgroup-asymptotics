import SymmetricSubgroupAsymptotics.CFSGE6GeckMiddleRootCharacters
import SymmetricSubgroupAsymptotics.CFSGE6GeckProductTorusWordAction
import SymmetricSubgroupAsymptotics.CFSGE6GeckMiddleFactorInjective

/-! Genuine product-torus action on the two literal middle A3 factors.
The paired factor requires just equality of its two original simple
scalars; the application to folded F4 supplies this equality. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckMiddleProductTorusAction
open CFSGE6GeckMiddleRootCharacters CFSGE6GeckProductTorusWordAction
open CFSGE6GeckProductTorus CFSGIntegerMatrixPowerHom
open CFSGE6GeckMiddleAThreeCollecting CFSGE6GeckMiddleFactorInjective
open CFSGE6GeckSignedSimpleParameters CFSGTwistedE6GeckDiagramCovariance
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord CFSGSerreQuadraticWordRootTransport
local notation "A" => CartanMatrix.E₆

private theorem pair_as_words (K : Type) [Field K] (a : K) :
    middlePair K (RingEquiv.refl K) a=
      rootWord rawData K [3] false 2 a*rootWord rawData K [3] false 4 a := by
  change canonicalWeyl rawData K 3*
    (canonicalRoot rawData K false 2 a*canonicalRoot rawData K false 4 a)*
      (canonicalWeyl rawData K 3)⁻¹=
    ((canonicalWeyl rawData K 3*1)*canonicalRoot rawData K false 2 a*
      (canonicalWeyl rawData K 3*1)⁻¹)*
    ((canonicalWeyl rawData K 3*1)*canonicalRoot rawData K false 4 a*
      (canonicalWeyl rawData K 3*1)⁻¹)
  group

private theorem conjugate_product {G : Type*} [Group G] (g x y : G) :
    g*(x*y)*g⁻¹=(g*x*g⁻¹)*(g*y*g⁻¹) := by group

theorem product_torus_highestMiddle (K : Type) [Field K] (x : Fin 6 → Kˣ) (a : K) :
    rawProductTorus K x*highestMiddle K a*(rawProductTorus K x)⁻¹=
      highestMiddle K (a*((powerHom A x 2*powerHom A x 3)*powerHom A x 4 : Kˣ)) := by
  have h := product_torus_positive_word_action K x [2,4] 3 a
  rw [highest_character] at h
  simpa only [rootWord,canonicalWord,mul_one,highestMiddle] using h

theorem product_torus_middlePair (K : Type) [Field K] (x : Fin 6 → Kˣ)
    (h24 : powerHom A x 2=powerHom A x 4) (a : K) :
    rawProductTorus K x*middlePair K (RingEquiv.refl K) a*(rawProductTorus K x)⁻¹=
      middlePair K (RingEquiv.refl K) (a*(powerHom A x 2*powerHom A x 3 : Kˣ)) := by
  rw [pair_as_words,conjugate_product]
  rw [product_torus_positive_word_action,product_torus_positive_word_action,
    paired_first_character,paired_second_character]
  have he : powerHom A x 3*powerHom A x 4=powerHom A x 2*powerHom A x 3 := by
    rw [←h24,mul_comm]
  rw [he,←pair_as_words]

end SymmetricSubgroupAsymptotics.CFSGE6GeckMiddleProductTorusAction
