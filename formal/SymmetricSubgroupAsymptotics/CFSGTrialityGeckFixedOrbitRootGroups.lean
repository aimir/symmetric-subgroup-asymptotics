import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOrbitZeroFunctionalGroup
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedShortComplementFactor
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortCentralizerCardinality
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckSectionParameterRanges
import SymmetricSubgroupAsymptotics.CFSGTrialityFixedField
import SymmetricSubgroupAsymptotics.CFSGCentralTwistedCommutatorLift
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOuterParameterChart

/-! Exact parameters of the two actual fixed positive orbit root groups.
The outer orbit retains the cubic extension, whereas the middle root
retains the fixed field. These are literal fixed matrices, not lifted
fixed classes or an abstract rank-one recognition premise. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedOrbitRootGroups
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckOrbitZeroFunctionalGroup CFSGTrialityGeckShortComplementFactor
open CFSGTrialityGeckFixedShortComplementFactor CFSGTrialityGeckFixedRootWords
open CFSGTrialityGeckShortCentralizerCardinality CFSGTrialityGeckSectionParameterRanges
open CFSGTrialityGeckFixedRootSections CFSGTrialityGeckMatrixTwist
open CFSGTrialityGeckRootSubgroupTwist CFSGTrialityFixedField CFSGSerreOrdinaryTwists
open CFSGSerreQuadraticMatrix CFSGCentralTwistedCommutatorLift
open CFSGTrialityGeckOuterParameterChart
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _

theorem canonical_middle_injective (K : Type) [Field K] [Finite K] :
    Function.Injective (canonicalRoot rawData K false 1) := by
  intro t u he
  apply (longParameter_bijective K 0).1
  apply Subtype.ext
  simpa only [longParameter,longSection,longTransport,Matrix.cons_val_zero,
    one_mul,inv_one,mul_one] using he

def fixedOrbitRootGroup (q : CFSG.PrimePower) (a : Bool) :
    Subgroup (Matrix GeckIndex GeckIndex (q.Extension 3))ˣ :=
  orbitRootGroup (q.Extension 3) a ⊓
    fixedSubgroup (unitTwist (q.Extension 3) (definingFieldAutomorphism q 3))

theorem shortOrbit_mem_outer (K : Type) [Field K] (sigma : K ≃+* K) (t : K) :
    shortOrbit K sigma false t ∈ outerGroup K := by
  refine ⟨![Multiplicative.ofAdd t,Multiplicative.ofAdd (sigma t),
    Multiplicative.ofAdd (sigma (sigma t))],?_⟩
  rw [outerProductHom_explicit]
  rfl

def shortFixedParameter (q : CFSG.PrimePower) (t : q.Extension 3) :
    fixedOrbitRootGroup q false :=
  ⟨shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) false t,
    shortOrbit_mem_outer _ _ t,actual_shortOrbit_fixed q false t⟩

theorem shortFixedParameter_bijective (q : CFSG.PrimePower) :
    Function.Bijective (shortFixedParameter q) := by
  constructor
  · intro t u he
    exact shortOrbit_injective (q.Extension 3) (definingFieldAutomorphism q 3)
      (congrArg Subtype.val he)
  · intro u
    obtain ⟨t,_,he⟩ := exists_short_orbit_of_outer_fixed (q.Extension 3)
      (definingFieldAutomorphism q 3) u.val u.property.1 u.property.2
    exact ⟨t,Subtype.ext he.symm⟩

def middleFixedParameter (q : CFSG.PrimePower) (t : fixedField q) :
    fixedOrbitRootGroup q true := by
  refine ⟨canonicalRoot rawData (q.Extension 3) false 1 t.val,?_,?_⟩
  · exact ⟨t.val,rfl⟩
  · change unitTwist (q.Extension 3) (definingFieldAutomorphism q 3)
      (canonicalRoot rawData (q.Extension 3) false 1 t.val)=
        canonicalRoot rawData (q.Extension 3) false 1 t.val
    rw [unitTwist_raw_root]
    change canonicalRoot rawData (q.Extension 3) false 1
      (definingFieldAutomorphism q 3 t.val)=canonicalRoot rawData (q.Extension 3) false 1 t.val
    have ht : definingFieldAutomorphism q 3 t.val=t.val := t.property
    rw [ht]

theorem middleFixedParameter_bijective (q : CFSG.PrimePower) :
    Function.Bijective (middleFixedParameter q) := by
  constructor
  · intro t u he
    apply Subtype.ext
    exact canonical_middle_injective (q.Extension 3) (congrArg Subtype.val he)
  · intro u
    obtain ⟨t,ht⟩ := u.property.1
    have hfixed : unitTwist (q.Extension 3) (definingFieldAutomorphism q 3)
        (canonicalRoot rawData (q.Extension 3) false 1 t)=
      canonicalRoot rawData (q.Extension 3) false 1 t := by
      rw [ht]
      exact u.property.2
    rw [unitTwist_raw_root] at hfixed
    have htf : definingFieldAutomorphism q 3 t=t := by
      apply canonical_middle_injective (q.Extension 3)
      exact hfixed
    exact ⟨⟨t,htf⟩,Subtype.ext ht⟩

theorem fixedOrbitRootGroup_short_card (q : CFSG.PrimePower) :
    Nat.card (fixedOrbitRootGroup q false)=q.order^3 := by
  have he := (Nat.card_congr (Equiv.ofBijective (shortFixedParameter q)
    (shortFixedParameter_bijective q))).symm
  exact he.trans (CFSGTrialityTripleFixedRoots.extension_three_card q)

theorem fixedOrbitRootGroup_middle_card (q : CFSG.PrimePower) :
    Nat.card (fixedOrbitRootGroup q true)=q.order := by
  have he := (Nat.card_congr (Equiv.ofBijective (middleFixedParameter q)
    (middleFixedParameter_bijective q))).symm
  exact he.trans (fixedField_card q)

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedOrbitRootGroups
