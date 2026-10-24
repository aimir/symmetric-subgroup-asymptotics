import SymmetricSubgroupAsymptotics.CFSGE6GeckOrthogonalPairChart
import Mathlib.GroupTheory.NoncommCoprod

/-! Three independent parameters on the orthogonal E6 simple nodes
0,5,1. The chart is a genuine homomorphism, its image is the join of the
root ranges, and the actual leading coordinates recover every parameter.
No coefficient-field restriction or root census is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckOuterTripleChart
open CFSGE6GeckSignedSimpleParameters CFSGE6GeckOrthogonalPairChart
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckPositiveTwist
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoGeckOrthogonalWeyl CFSGSerreQuadraticMatrix
open CFSGNormTwoCoordinateLeadingHom CFSGNormTwoCoordinateLeadingFactor
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

private theorem pair_single_commute (K : Type) [Field K]
    (a : Multiplicative K×Multiplicative K) (b : Multiplicative K) :
    Commute (rawPairHom K false 0 a) (rawSimpleHom K false 1 b) := by
  change Commute (canonicalRoot rawData K false 0 a.1.toAdd*
    canonicalRoot rawData K false 5 a.2.toAdd) (canonicalRoot rawData K false 1 b.toAdd)
  exact (orthogonal_signed_roots A hs hp E6Base E6Index K 0 1
    (by rw [E6_cartan];decide) false false a.1.toAdd b.toAdd).mul_left
      (orthogonal_signed_roots A hs hp E6Base E6Index K 5 1
        (by rw [E6_cartan];decide) false false a.2.toAdd b.toAdd)

def rawTripleHom (K : Type) [Field K] :
    (Multiplicative K×Multiplicative K)×Multiplicative K→*
      (Matrix GeckIndex GeckIndex K)ˣ :=
  MonoidHom.noncommCoprod (rawPairHom K false 0) (rawSimpleHom K false 1)
    (pair_single_commute K)

theorem rawTripleHom_val (K : Type) [Field K]
    (a : (Multiplicative K×Multiplicative K)×Multiplicative K) :
    rawTripleHom K a=(canonicalRoot rawData K false 0 a.1.1.toAdd*
      canonicalRoot rawData K false 5 a.1.2.toAdd)*canonicalRoot rawData K false 1 a.2.toAdd := rfl

def triplePositive (K : Type) [Field K] :
    (Multiplicative K×Multiplicative K)×Multiplicative K→*Positive K :=
  (rawTripleHom K).codRestrict (Positive K) (fun a=>by
    rw [rawTripleHom_val]
    exact (Positive K).mul_mem
      ((Positive K).mul_mem (positiveRoot A hd hs hp ho K 0 a.1.1.toAdd).property
        (positiveRoot A hd hs hp ho K 5 a.1.2.toAdd).property)
      (positiveRoot A hd hs hp ho K 1 a.2.toAdd).property)

theorem triple_leading (K : Type) [Field K]
    (a : (Multiplicative K×Multiplicative K)×Multiplicative K) :
    leadingHom A hd hs hp ho K (triplePositive K a)=Multiplicative.ofAdd
      (Pi.single 0 a.1.1.toAdd+Pi.single 5 a.1.2.toAdd+Pi.single 1 a.2.toAdd) := by
  have he : triplePositive K a=(positiveRoot A hd hs hp ho K 0 a.1.1.toAdd*
      positiveRoot A hd hs hp ho K 5 a.1.2.toAdd)*
        positiveRoot A hd hs hp ho K 1 a.2.toAdd := rfl
  rw [he,map_mul,map_mul,leadingHom_positiveRoot,leadingHom_positiveRoot,leadingHom_positiveRoot]
  rfl

theorem triplePositive_injective (K : Type) [Field K] :
    Function.Injective (triplePositive K) := by
  intro a b he
  have hh := congrArg (leadingHom A hd hs hp ho K) he
  rw [triple_leading,triple_leading] at hh
  apply Prod.ext
  · apply Prod.ext
    · apply (Multiplicative.toAdd : Multiplicative K≃K).injective
      simpa [Pi.single_apply] using congrArg
        (fun z : Multiplicative (Fin 6→K)=>z.toAdd 0) hh
    · apply (Multiplicative.toAdd : Multiplicative K≃K).injective
      simpa [Pi.single_apply] using congrArg
        (fun z : Multiplicative (Fin 6→K)=>z.toAdd 5) hh
  · apply (Multiplicative.toAdd : Multiplicative K≃K).injective
    simpa [Pi.single_apply] using congrArg
      (fun z : Multiplicative (Fin 6→K)=>z.toAdd 1) hh

theorem rawTripleHom_injective (K : Type) [Field K] :
    Function.Injective (rawTripleHom K) := by
  intro a b he
  exact triplePositive_injective K (Subtype.ext he)

theorem rawTripleHom_range (K : Type) [Field K] :
    (rawTripleHom K).range=(rawPairHom K false 0).range⊔(rawSimpleHom K false 1).range :=
  MonoidHom.noncommCoprod_range _ _ _

end SymmetricSubgroupAsymptotics.CFSGE6GeckOuterTripleChart
