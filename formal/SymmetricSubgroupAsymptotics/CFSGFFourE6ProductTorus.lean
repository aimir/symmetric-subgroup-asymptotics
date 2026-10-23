import SymmetricSubgroupAsymptotics.CFSGFFourRelativeScalarIndex
import SymmetricSubgroupAsymptotics.CFSGFFourE6ScalarTuple
import SymmetricSubgroupAsymptotics.CFSGFFourE6RelativeTorus
import SymmetricSubgroupAsymptotics.CFSGE6GeckProductTorus

/-! The four native F4 torus coordinates give an actual homomorphism
into J. Its literal six-node E6 value realizes exactly the determinant
one relative Cartan exponent map. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6ProductTorus
open CFSGFFourRelativeScalarIndex CFSGFFourE6RelativeTorus
open CFSGFFourE6GeneratedOriginalProjection CFSGTwistedE6GeckRelativeRootGenerated
open CFSGE6GeckRelativeScalarTuples CFSGE6GeckProductTorus
open CFSGIntegerMatrixPowerHom CFSG.Models.Chevalley
open CFSGFFourE6ScalarTuple CFSGE6GeckPairedParameterizedWeyl
open CFSGNormTwoGeckParameterizedTorus CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite

abbrev torusTuple (K : Type) [Field K] : (Fin 4→Kˣ)→*(Fin 6→Kˣ) := scalarTupleHom

theorem powerHom_torusTuple (K : Type) [Field K] (x : Fin 4→Kˣ) :
    powerHom (G := Kˣ) CartanMatrix.E₆ (torusTuple K x)=
      torusTuple K (powerHom (G := Kˣ) relativeCartan x) := powerHom_scalarTuple x

def fixedTorusTuple (K : Type) [Field K] (x : Fin 4→Kˣ) :
    relativeScalars K (RingEquiv.refl K) :=
  ⟨torusTuple K x,by
    intro i
    fin_cases i <;> apply Units.ext <;> rfl⟩

def torusWord (K : Type) [Field K] (x : Fin 4→Kˣ) : fixedRootGenerated K (RingEquiv.refl K) :=
  torusInGenerated K 0 (x 0)*(torusInGenerated K 1 (x 1)*
    (torusInGenerated K 3 (x 3)*torusInGenerated K 2 (x 2)))

theorem torusWord_val (K : Type) [Field K] (x : Fin 4→Kˣ) :
    (torusWord K x).val=rawProductTorus K (torusTuple K x) := by
  change (torusInGenerated K 0 (x 0)).val*((torusInGenerated K 1 (x 1)).val*
    ((torusInGenerated K 3 (x 3)).val*(torusInGenerated K 2 (x 2)).val))=_
  have h0 : (torusInGenerated K 0 (x 0)).val=pairedParameterTorus K (RingEquiv.refl K) 0 (x 0) :=
    torusInGenerated_paired_val K 0 (x 0)
  have h1 : (torusInGenerated K 1 (x 1)).val=pairedParameterTorus K (RingEquiv.refl K) 1 (x 1) :=
    torusInGenerated_paired_val K 1 (x 1)
  have h3 : (torusInGenerated K 3 (x 3)).val=
      parameterTorus CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K 1 (x 3) :=
    torusInGenerated_singleton_val K 0 (x 3)
  have h2 : (torusInGenerated K 2 (x 2)).val=
      parameterTorus CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K 3 (x 2) :=
    torusInGenerated_singleton_val K 1 (x 2)
  rw [h0,h1,h3,h2]
  exact (rawProductTorus_orbit_factors K (RingEquiv.refl K) (fixedTorusTuple K x)).symm

def productTorusGenerated (K : Type) [Field K] :
    (Fin 4→Kˣ)→*fixedRootGenerated K (RingEquiv.refl K) :=
  ((rawProductTorus K).comp (torusTuple K)).codRestrict _ (fun x => by
    change rawProductTorus K (torusTuple K x)∈_
    rw [←torusWord_val K x]
    exact (torusWord K x).property)

@[simp] theorem productTorusGenerated_val (K : Type) [Field K] (x : Fin 4→Kˣ) :
    (productTorusGenerated K x).val=rawProductTorus K (torusTuple K x) := rfl

def originalProductTorusHom (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] : (Fin 4→Kˣ)→*Projective CartanMatrix.F₄ K :=
  (generatedToOriginal K).comp (productTorusGenerated K)

end SymmetricSubgroupAsymptotics.CFSGFFourE6ProductTorus
