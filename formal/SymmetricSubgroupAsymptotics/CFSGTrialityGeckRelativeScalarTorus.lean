import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMixedTorusConjugation
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckSignedSimpleParameters
import Mathlib.Tactic.Ring

/-! A literal word in the same triality generated group realizes every
pair of nonzero scalar actions on the two positive simple parameter
charts. This binds the cubic norm scalar calculation to actual matrices;
no supplied torus-recognition hypothesis is used. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckRelativeScalarTorus
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckFixedRootWords CFSGTrialityGeckShortParameterWeyl
open CFSGTrialityGeckShortTorusConjugation CFSGTrialityGeckMixedTorusConjugation
open CFSGTrialityGeckRelativeRootGenerated CFSGTrialityFixedField
open CFSGTrialityNormTorusScalars CFSGSerreOrdinaryTwists
open CFSGNormTwoGeckParameterizedTorus CFSGNormTwoGeckParameterizedWeyl
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _

theorem shortTorusWord_mem_generated (q : CFSG.PrimePower) (c : (q.Extension 3)ˣ) :
    shortTorusWord (q.Extension 3) (definingFieldAutomorphism q 3) c∈
      fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3) := by
  let J := fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3)
  have hw (a : (q.Extension 3)ˣ) :
      shortWeylWord (q.Extension 3) (definingFieldAutomorphism q 3) a∈J := by
    apply J.mul_mem
    · exact J.mul_mem (shortOrbit_mem_generated _ _ false _ (sigma_thrice q _))
        (shortOrbit_mem_generated _ _ true _ (sigma_thrice q _))
    · exact shortOrbit_mem_generated _ _ false _ (sigma_thrice q _)
  exact J.mul_mem (hw c) (J.inv_mem (hw 1))

theorem middleTorus_mem_generated (q : CFSG.PrimePower) (a : (fixedField q)ˣ) :
    middleTorus (q.Extension 3) (embedUnits q a)∈
      fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3) := by
  let J := fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3)
  have hw (b : (fixedField q)ˣ) :
      parameterWeyl (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite Base Index (q.Extension 3) 1 (embedUnits q b)∈J := by
    have hb : definingFieldAutomorphism q 3 b.val.val=b.val.val := b.val.property
    change CFSGSerreQuadraticMatrix.canonicalRoot rawData (q.Extension 3) false 1 b.val.val*
      CFSGSerreQuadraticMatrix.canonicalRoot rawData (q.Extension 3) true 1 (-b.val.val⁻¹)*
      CFSGSerreQuadraticMatrix.canonicalRoot rawData (q.Extension 3) false 1 b.val.val∈J
    exact J.mul_mem (J.mul_mem (central_root_mem_generated _ _ false _ hb)
      (central_root_mem_generated _ _ true _ (by simp only [map_neg,map_inv₀,hb])))
      (central_root_mem_generated _ _ false _ hb)
  have h1 : parameterWeyl (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index (q.Extension 3) 1 1∈J := by
    simpa only [map_one] using hw 1
  exact J.mul_mem (hw a) (J.inv_mem h1)

def relativeTorusWord (q : CFSG.PrimePower)
    (c : (q.Extension 3)ˣ) (a : (fixedField q)ˣ) :
    (Matrix GeckIndex GeckIndex (q.Extension 3))ˣ :=
  shortTorusWord (q.Extension 3) (definingFieldAutomorphism q 3) c*
    middleTorus (q.Extension 3) (embedUnits q a)

theorem relativeTorusWord_mem_generated (q : CFSG.PrimePower)
    (c : (q.Extension 3)ˣ) (a : (fixedField q)ˣ) :
    relativeTorusWord q c a∈fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3) :=
  (fixedRootGenerated _ _).mul_mem (shortTorusWord_mem_generated q c)
    (middleTorus_mem_generated q a)

theorem relativeTorusWord_short (q : CFSG.PrimePower)
    (c : (q.Extension 3)ˣ) (a : (fixedField q)ˣ) (t : q.Extension 3) :
    relativeTorusWord q c a*shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) false t*
      (relativeTorusWord q c a)⁻¹ =
    shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) false
      ((((CFSGCubicNormTorusScalars.scalarMap (embedUnits q) (normUnits q) (c,a)).1 :
        (q.Extension 3)ˣ) : q.Extension 3)*t) := by
  let S := shortTorusWord (q.Extension 3) (definingFieldAutomorphism q 3) c
  let M := middleTorus (q.Extension 3) (embedUnits q a)
  have ha : definingFieldAutomorphism q 3 ((embedUnits q a : (q.Extension 3)ˣ) : q.Extension 3)=
      ((embedUnits q a : (q.Extension 3)ˣ) : q.Extension 3) := a.val.property
  calc
    _=S*(M*shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) false t*M⁻¹)*S⁻¹ := by
      dsimp only [relativeTorusWord,S,M]
      group
    _=_ := by
      dsimp only [S,M]
      rw [middleTorus_short _ _ _ ha,shortTorusWord_conjugate]
      congr 1
      simp only [CFSGCubicNormTorusScalars.scalarMap,Units.val_mul,
        Units.val_pow_eq_pow_val,Units.val_inv_eq_inv_val,embedUnits,Units.coe_map]
      change (t*a.val.val⁻¹)*(c:q.Extension 3)^2=((c:q.Extension 3)^2*a.val.val⁻¹)*t
      ring

theorem relativeTorusWord_middle (q : CFSG.PrimePower)
    (c : (q.Extension 3)ˣ) (a : (fixedField q)ˣ) (t : fixedField q) :
    relativeTorusWord q c a*CFSGSerreQuadraticMatrix.canonicalRoot rawData (q.Extension 3) false 1 t.val*
      (relativeTorusWord q c a)⁻¹ =
    CFSGSerreQuadraticMatrix.canonicalRoot rawData (q.Extension 3) false 1
      (((((CFSGCubicNormTorusScalars.scalarMap (embedUnits q) (normUnits q) (c,a)).2 :
        (fixedField q)ˣ) : fixedField q)*t).val) := by
  let S := shortTorusWord (q.Extension 3) (definingFieldAutomorphism q 3) c
  let M := middleTorus (q.Extension 3) (embedUnits q a)
  calc
    _=S*(M*CFSGSerreQuadraticMatrix.canonicalRoot rawData (q.Extension 3) false 1 t.val*M⁻¹)*S⁻¹ := by
      dsimp only [relativeTorusWord,S,M]
      group
    _=_ := by
      dsimp only [S,M]
      rw [middleTorus_middle,shortTorus_middle]
      congr 1
      simp only [CFSGCubicNormTorusScalars.scalarMap,Units.val_mul,
        Units.val_pow_eq_pow_val,Units.val_inv_eq_inv_val,embedUnits,normUnits,Units.coe_map,
        Subfield.coe_mul,Subfield.coe_inv]
      change (t.val*a.val.val^2)*
          ((c:q.Extension 3)*definingFieldAutomorphism q 3 (c:q.Extension 3)*
            definingFieldAutomorphism q 3 (definingFieldAutomorphism q 3 (c:q.Extension 3)))⁻¹=
        (a.val.val^2*((c:q.Extension 3)*definingFieldAutomorphism q 3 (c:q.Extension 3)*
            definingFieldAutomorphism q 3 (definingFieldAutomorphism q 3 (c:q.Extension 3)))⁻¹)*t.val
      ring

theorem exists_scalar_word (q : CFSG.PrimePower)
    (x : (q.Extension 3)ˣ) (y : (fixedField q)ˣ) :
    ∃d∈fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3),
      (∀t,d*shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) false t*d⁻¹=
        shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) false ((x:q.Extension 3)*t))∧
      (∀t:fixedField q,d*CFSGSerreQuadraticMatrix.canonicalRoot rawData (q.Extension 3) false 1 t.val*d⁻¹=
        CFSGSerreQuadraticMatrix.canonicalRoot rawData (q.Extension 3) false 1 ((y:fixedField q)*t).val) := by
  obtain ⟨⟨c,a⟩,hca⟩ := scalarMap_surjective q (x,y)
  refine ⟨relativeTorusWord q c a,relativeTorusWord_mem_generated q c a,?_,?_⟩
  · intro t
    simpa only [hca] using relativeTorusWord_short q c a t
  · intro t
    simpa only [hca] using relativeTorusWord_middle q c a t

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckRelativeScalarTorus
