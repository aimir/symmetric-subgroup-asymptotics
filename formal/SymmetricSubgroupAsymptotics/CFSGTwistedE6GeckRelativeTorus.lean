import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalSingletonSignedField
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalPairedSignedField
import SymmetricSubgroupAsymptotics.CFSGE6GeckPairedParameterizedWeyl
import SymmetricSubgroupAsymptotics.CFSGSemilinearRankOneWord

/-! Actual relative rank-one tori in J and their projected Weyl images.
They are built from the displayed signed simple charts; no arbitrary
original automorphism is lifted. Signed field data controls the image of
each original simple Weyl word by the SAME literal torus factor. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRelativeTorus
open CFSGTwistedE6GeckOriginalPairedA2 CFSGTwistedE6GeckOriginalSingletonA2
open CFSGTwistedE6GeckOriginalSimpleParameters CFSGTwistedE6GeckOriginalRankOneWitness
open CFSGTwistedE6GeckOriginalOppositeAlignment CFSGTwistedE6GeckOriginalProjection
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckDiagramCovariance
open CFSGTwistedE6RelativeWeylOrbits CFSGE6GeckFixedOrbitRootGroups
open CFSGE6GeckFixedSimpleParameters CFSGTwistedE6FixedA2 CFSGTwistedE6PairedFixedRoots
open CFSGE6GeckPairedParameterizedWeyl CFSGTwistedE6GeckPairedA2Commutator
open CFSGNormTwoGeckParameterizedWeyl CFSGNormTwoGeckParameterizedTorus CFSGNormTwoGeckSimpleGaussFactor
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord CFSGSerreOrdinaryTwists
open CFSGSemilinearRankOneWord

def coefficientUnit (q : CFSG.PrimePower) (t : (Coefficient q)ˣ) : (q.Extension 2)ˣ :=
  (Units.map (Coefficient q).subtype.toMonoidHom) t

def singletonSignedInGenerated (q : CFSG.PrimePower) (neg : Bool) (j : Fin 2) :
    Multiplicative (Coefficient q)→*fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2) :=
  (signedFixedToGenerated q neg).comp
    (singletonFixedHom (q.Extension 2) (definingFieldAutomorphism q 2) neg j)

def pairedSignedInGenerated (q : CFSG.PrimePower) (neg : Bool) (j : Fin 2) :
    Multiplicative (q.Extension 2)→*fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2) :=
  (signedFixedToGenerated q neg).comp
    (pairedFixedHom (q.Extension 2) (definingFieldAutomorphism q 2) (coefficient_involutive q) neg j)

def singletonScaledWeylGenerated (q : CFSG.PrimePower) (j : Fin 2) (t : (Coefficient q)ˣ) :
    fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2) :=
  singletonSignedInGenerated q false j (Multiplicative.ofAdd (t : Coefficient q))*
    singletonSignedInGenerated q true j (Multiplicative.ofAdd (-(t : Coefficient q)⁻¹))*
    singletonSignedInGenerated q false j (Multiplicative.ofAdd (t : Coefficient q))

def pairedScaledWeylGenerated (q : CFSG.PrimePower) (j : Fin 2) (t : (q.Extension 2)ˣ) :
    fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2) :=
  pairedSignedInGenerated q false j (Multiplicative.ofAdd (t : q.Extension 2))*
    pairedSignedInGenerated q true j (Multiplicative.ofAdd (-(t : q.Extension 2)⁻¹))*
    pairedSignedInGenerated q false j (Multiplicative.ofAdd (t : q.Extension 2))

def singletonTorusGenerated (q : CFSG.PrimePower) (j : Fin 2) (t : (Coefficient q)ˣ) :
    fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2) :=
  singletonScaledWeylGenerated q j t*(simpleWeylGenerated q (singletonOrbit j))⁻¹

def pairedTorusGenerated (q : CFSG.PrimePower) (j : Fin 2) (t : (q.Extension 2)ˣ) :
    fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2) :=
  pairedScaledWeylGenerated q j t*(simpleWeylGenerated q (pairedOrbit j))⁻¹

theorem singletonTorusGenerated_val (q : CFSG.PrimePower) (j : Fin 2) (t : (Coefficient q)ˣ) :
    (singletonTorusGenerated q j t).val=
      parameterTorus CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index
        (q.Extension 2) (node j) (coefficientUnit q t) := by
  have hw : (simpleWeylGenerated q (singletonOrbit j)).val=canonicalWeyl rawData (q.Extension 2) (node j) := by
    rw [simpleWeylGenerated_val]
    fin_cases j <;> simp [singletonOrbit,orbitWord,canonicalWord,node]
  change (singletonScaledWeylGenerated q j t).val*(simpleWeylGenerated q (singletonOrbit j)).val⁻¹=_
  rw [hw,parameterTorus,CFSGNormTwoGeckWeylSquareTorus.parameterWeyl_one]
  rfl

theorem pairedTorusGenerated_val (q : CFSG.PrimePower) (j : Fin 2) (t : (q.Extension 2)ˣ) :
    (pairedTorusGenerated q j t).val=pairedParameterTorus (q.Extension 2) (definingFieldAutomorphism q 2) j t := by
  have hw : (simpleWeylGenerated q (pairedOrbit j)).val=pairedMatrixWeyl (q.Extension 2) j := by
    rw [simpleWeylGenerated_val]
    fin_cases j <;> simp [pairedOrbit,orbitWord,canonicalWord,pairedMatrixWeyl] <;> rfl
  change (pairedScaledWeylGenerated q j t).val*(simpleWeylGenerated q (pairedOrbit j)).val⁻¹=_
  rw [hw]
  rfl

theorem singleton_weyl_image (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedE6 q)]
    (f : MulAut (CFSG.Models.TwistedE6 q)) (j : Fin 2) (tau : RingAut (Coefficient q))
    (t : (Coefficient q)ˣ)
    (hpos : ∀a,f (singletonOriginalHom q false j (Multiplicative.ofAdd a))=
      singletonOriginalHom q false j (Multiplicative.ofAdd ((t : Coefficient q)*tau a)))
    (hneg : ∀a,f (singletonOriginalHom q true j (Multiplicative.ofAdd a))=
      singletonOriginalHom q true j (Multiplicative.ofAdd ((t : Coefficient q)⁻¹*tau a))) :
    f (generatedToOriginal q (simpleWeylGenerated q (singletonOrbit j)))=
      generatedToOriginal q (singletonTorusGenerated q j t)*
        generatedToOriginal q (simpleWeylGenerated q (singletonOrbit j)) := by
  let u := singletonOriginalHom q false j
  let v := singletonOriginalHom q true j
  have hp : generatedToOriginal q (orbitOneInGenerated q false (singletonOrbit j))=u (Multiplicative.ofAdd 1) :=
    originalOrbitOne_singleton q false j
  have hn : generatedToOriginal q (orbitOneInGenerated q true (singletonOrbit j))=v (Multiplicative.ofAdd 1) :=
    originalOrbitOne_singleton q true j
  have hW : generatedToOriginal q (simpleWeylGenerated q (singletonOrbit j))=
      u (Multiplicative.ofAdd 1)*(v (Multiplicative.ofAdd 1))⁻¹*u (Multiplicative.ofAdd 1) := by
    have hh := map_rank_one_word (generatedToOriginal q)
      (orbitOneInGenerated q false (singletonOrbit j)) (orbitOneInGenerated q true (singletonOrbit j))
    rw [hp,hn] at hh
    exact hh
  have hS : generatedToOriginal q (singletonScaledWeylGenerated q j t)=
      u (Multiplicative.ofAdd (t : Coefficient q))*v (Multiplicative.ofAdd (-(t : Coefficient q)⁻¹))*
        u (Multiplicative.ofAdd (t : Coefficient q)) :=
    map_three (generatedToOriginal q)
      (singletonSignedInGenerated q false j (Multiplicative.ofAdd (t : Coefficient q)))
      (singletonSignedInGenerated q true j (Multiplicative.ofAdd (-(t : Coefficient q)⁻¹)))
      (singletonSignedInGenerated q false j (Multiplicative.ofAdd (t : Coefficient q)))
  apply image_eq_torus_mul (generatedToOriginal q) f.toMonoidHom
    (singletonScaledWeylGenerated q j t) (simpleWeylGenerated q (singletonOrbit j))
  calc
    _=f (u (Multiplicative.ofAdd 1)*(v (Multiplicative.ofAdd 1))⁻¹*u (Multiplicative.ofAdd 1)) := congrArg f hW
    _=_ := (image_rank_one_word u v f.toMonoidHom tau t hpos hneg).trans hS.symm

theorem paired_weyl_image (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedE6 q)]
    (f : MulAut (CFSG.Models.TwistedE6 q)) (j : Fin 2) (tau : RingAut (q.Extension 2))
    (t : (q.Extension 2)ˣ)
    (hpos : ∀a,f (pairedOriginalHom q false j (Multiplicative.ofAdd a))=
      pairedOriginalHom q false j (Multiplicative.ofAdd ((t : q.Extension 2)*tau a)))
    (hneg : ∀a,f (pairedOriginalHom q true j (Multiplicative.ofAdd a))=
      pairedOriginalHom q true j (Multiplicative.ofAdd ((t : q.Extension 2)⁻¹*tau a))) :
    f (generatedToOriginal q (simpleWeylGenerated q (pairedOrbit j)))=
      generatedToOriginal q (pairedTorusGenerated q j t)*
        generatedToOriginal q (simpleWeylGenerated q (pairedOrbit j)) := by
  let u := pairedOriginalHom q false j
  let v := pairedOriginalHom q true j
  have hp : generatedToOriginal q (orbitOneInGenerated q false (pairedOrbit j))=u (Multiplicative.ofAdd 1) :=
    originalOrbitOne_paired q false j
  have hn : generatedToOriginal q (orbitOneInGenerated q true (pairedOrbit j))=v (Multiplicative.ofAdd 1) :=
    originalOrbitOne_paired q true j
  have hW : generatedToOriginal q (simpleWeylGenerated q (pairedOrbit j))=
      u (Multiplicative.ofAdd 1)*(v (Multiplicative.ofAdd 1))⁻¹*u (Multiplicative.ofAdd 1) := by
    have hh := map_rank_one_word (generatedToOriginal q)
      (orbitOneInGenerated q false (pairedOrbit j)) (orbitOneInGenerated q true (pairedOrbit j))
    rw [hp,hn] at hh
    exact hh
  have hS : generatedToOriginal q (pairedScaledWeylGenerated q j t)=
      u (Multiplicative.ofAdd (t : q.Extension 2))*v (Multiplicative.ofAdd (-(t : q.Extension 2)⁻¹))*
        u (Multiplicative.ofAdd (t : q.Extension 2)) :=
    map_three (generatedToOriginal q)
      (pairedSignedInGenerated q false j (Multiplicative.ofAdd (t : q.Extension 2)))
      (pairedSignedInGenerated q true j (Multiplicative.ofAdd (-(t : q.Extension 2)⁻¹)))
      (pairedSignedInGenerated q false j (Multiplicative.ofAdd (t : q.Extension 2)))
  apply image_eq_torus_mul (generatedToOriginal q) f.toMonoidHom
    (pairedScaledWeylGenerated q j t) (simpleWeylGenerated q (pairedOrbit j))
  calc
    _=f (u (Multiplicative.ofAdd 1)*(v (Multiplicative.ofAdd 1))⁻¹*u (Multiplicative.ofAdd 1)) := congrArg f hW
    _=_ := (image_rank_one_word u v f.toMonoidHom tau t hpos hneg).trans hS.symm

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRelativeTorus
