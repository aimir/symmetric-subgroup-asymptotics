import SymmetricSubgroupAsymptotics.CFSGE6GeckOrbitOneSignDetection
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckPositiveTwist

/-! Folded orbit parameters are literal ordered products of their root
factors. Negative word images are therefore certified factor by factor,
with no matrix expansion or parameter-faithfulness assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckOrbitParameterWordMembership
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckDiagramCovariance
open CFSGTwistedE6RelativeWeylOrbits CFSGTwistedE6FixedWordClassification
open CFSGTwistedE6WeylChamber
open CFSGSerreQuadraticMatrix CFSGNormTwoCoordinateWeylRootMembership
open CFSGNormTwoGeckWeylWordDegree CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

theorem orbitParameter_list_prod (K : Type) [Field K] (neg : Bool) (a : Fin 4) (t : K) :
    orbitParameter K neg a t=((orbitWord a).map (fun i=>canonicalRoot rawData K neg i t)).prod := by
  fin_cases a <;> simp [orbitWord,orbitParameter]

theorem negative_conjugate_orbit_one (K : Type) [Field K] (r : List (Fin 4)) (a : Fin 4)
    (hall : ∀i∈orbitWord a,∀j,(rootAction (expandRelative r) (E6Index i)).val j≤0) :
    wordUnit A hs hp E6Base E6Index K (expandRelative r)*orbitParameter K false a 1*
      (wordUnit A hs hp E6Base E6Index K (expandRelative r))⁻¹∈CFSGTwistedE6GeckPositiveTwist.Negative K := by
  let f := (MulAut.conj (wordUnit A hs hp E6Base E6Index K (expandRelative r))).toMonoidHom
  change f (orbitParameter K false a 1)∈CFSGTwistedE6GeckPositiveTwist.Negative K
  have hi (i : Fin 6) (him : i∈orbitWord a) :
      f (canonicalRoot rawData K false i 1)∈CFSGTwistedE6GeckPositiveTwist.Negative K :=
    negative_word_mem A hd hs hp ho K (expandRelative r) i 1 (hall i him)
  rw [orbitParameter_list_prod,map_list_prod]
  apply (CFSGTwistedE6GeckPositiveTwist.Negative K).list_prod_mem
  intro x hx
  obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
  obtain ⟨i,him,rfl⟩ := List.mem_map.mp hy
  exact hi i him

end SymmetricSubgroupAsymptotics.CFSGE6GeckOrbitParameterWordMembership
