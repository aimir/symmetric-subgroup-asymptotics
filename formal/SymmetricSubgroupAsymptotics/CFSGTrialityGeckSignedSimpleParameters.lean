import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedOrbitRootGroups
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckSimpleChartWeyl
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortOrbitCommutator
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckRelativeRootGenerated

/-! Literal additive parameter homomorphisms for all four signed simple
relative root groups, with actual injectivity and genuine J membership.
The negative parameters are separated by the fixed simple Weyl word;
no field-recognition or source-faithfulness assumption is supplied. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckSignedSimpleParameters
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckFixedOrbitRootGroups CFSGTrialityGeckSimpleChartWeyl
open CFSGTrialityGeckFixedRootWords CFSGTrialityGeckShortOrbitCommutator
open CFSGTrialityGeckSimpleOrbitFlags CFSGTrialityGeckRelativeRootGenerated
open CFSGTrialityGeckShortCentralizerCardinality CFSGTrialityFixedField
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord CFSGSerreOrdinaryTwists
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _

private theorem negative_parameter_injective {K G : Type*} [AddGroup K] [Group G]
    (e : MulAut G) (x y : K→G) (he : ∀t,e (x t)=y (-t))
    (hx : Function.Injective x) : Function.Injective y := by
  intro t u htu
  have hneg : x (-t)=x (-u) := by
    apply e.injective
    calc
      e (x (-t))=y t := by simpa only [neg_neg] using he (-t)
      _=y u := htu
      _=e (x (-u)) := by simpa only [neg_neg] using (he (-u)).symm
  exact neg_injective (hx hneg)

theorem short_parameter_injective (q : CFSG.PrimePower) (neg : Bool) :
    Function.Injective (shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) neg) := by
  cases neg
  · exact shortOrbit_injective _ _
  · exact negative_parameter_injective
      (MulAut.conj (canonicalWord rawData (q.Extension 3) (orbitWord false))) _ _
      (short_word_conjugates _ _) (shortOrbit_injective _ _)

def middleRawHom (q : CFSG.PrimePower) (neg : Bool) :
    Multiplicative (fixedField q)→*(Matrix GeckIndex GeckIndex (q.Extension 3))ˣ where
  toFun t := canonicalRoot rawData (q.Extension 3) neg 1 t.toAdd.val
  map_one' := canonicalRoot_zero rawData (q.Extension 3) neg 1
  map_mul' t u := (canonicalRoot_add rawData (q.Extension 3) neg 1 t.toAdd.val u.toAdd.val).symm

theorem middleRawHom_injective (q : CFSG.PrimePower) (neg : Bool) :
    Function.Injective (middleRawHom q neg) := by
  have hpos : Function.Injective (fun t:fixedField q=>canonicalRoot rawData (q.Extension 3) false 1 t.val) := by
    intro t u he
    exact Subtype.ext (canonical_middle_injective (q.Extension 3) he)
  have hraw : Function.Injective (fun t:fixedField q=>canonicalRoot rawData (q.Extension 3) neg 1 t.val) := by
    cases neg
    · exact hpos
    · apply negative_parameter_injective
        (MulAut.conj (canonicalWord rawData (q.Extension 3) (orbitWord true))) _ _ _ hpos
      intro t
      exact middle_word_conjugates (q.Extension 3) t.val
  intro t u he
  exact hraw he

def shortGeneratedHom (q : CFSG.PrimePower) (neg : Bool) :
    Multiplicative (q.Extension 3)→*
      fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3) :=
  (shortOrbitHom (q.Extension 3) (definingFieldAutomorphism q 3) neg).codRestrict _
    (fun t=>shortOrbit_mem_generated _ _ neg t.toAdd
      (CFSGTrialityTripleFixedRoots.extension_three_pow_thrice q t.toAdd))

def middleGeneratedHom (q : CFSG.PrimePower) (neg : Bool) :
    Multiplicative (fixedField q)→*
      fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3) :=
  (middleRawHom q neg).codRestrict _
    (fun t=>central_root_mem_generated _ _ neg t.toAdd.val t.toAdd.property)

theorem shortGeneratedHom_val (q : CFSG.PrimePower) (neg : Bool) (t : Multiplicative (q.Extension 3)) :
    (shortGeneratedHom q neg t).val=shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) neg t.toAdd := rfl

theorem middleGeneratedHom_val (q : CFSG.PrimePower) (neg : Bool) (t : Multiplicative (fixedField q)) :
    (middleGeneratedHom q neg t).val=canonicalRoot rawData (q.Extension 3) neg 1 t.toAdd.val := rfl

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckSignedSimpleParameters
