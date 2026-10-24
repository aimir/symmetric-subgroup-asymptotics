import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedWordSimpleSigns

/-! A single actual folded root parameter at one detects a negative
relative simple image. This works in characteristic two and needs no
field-parameter separation or exceptional root-duality map. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckOrbitOneSignDetection
open CFSGTwistedE6GeckFixedWordSimpleSigns CFSGTwistedE6GeckFixedSimpleTests
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckPositiveTwist
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6WeylChamber
open CFSGTwistedE6RelativeWeylOrbits CFSGTwistedE6FixedWordClassification
open CFSGNormTwoCoordinateWeylRootMembership CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckOppositeIntersection
open CFSGNormTwoCoordinateHeight CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite
open CFSGSerreDiagram
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

private theorem orbit_nodes_pair (a : Fin 4) (i j : Fin 6)
    (hi : i∈orbitWord a) (hj : j∈orbitWord a) : j=i ∨ j=e6Permutation i := by
  have h : ∀a : Fin 4,∀i j : Fin 6,
      i∈orbitWord a→j∈orbitWord a→j=i ∨ j=e6Permutation i := by decide +kernel
  exact h a i j hi hj

theorem nonpositive_of_orbit_one_negative (K : Type) [Field K]
    (r : List (Fin 4)) (a : Fin 4)
    (hnegative : wordUnit A hs hp E6Base E6Index K (expandRelative r)*
      orbitParameter K false a 1*
      (wordUnit A hs hp E6Base E6Index K (expandRelative r))⁻¹∈
        rootGroup A hs hp E6Base E6Index K true) :
    ∀i∈orbitWord a,∀j,(rootAction (expandRelative r) (E6Index i)).val j≤0 := by
  intro i hi
  rcases word_sign_membership A hd hs hp ho K (expandRelative r) i 1 with hpos|hneg
  · have hall : ∀j∈orbitWord a,∀k,0≤(rootAction (expandRelative r) (E6Index j)).val k := by
      intro j hj
      rcases orbit_nodes_pair a i j hi hj with hji|hji
      · rw [hji]
        exact hpos.1
      · rw [hji]
        exact positive_simple_partner (expandRelative r) (relative_root_action_commutes r) i hpos.1
    have hpositive := positive_conjugate_orbit K r a hall
    have hboth : wordUnit A hs hp E6Base E6Index K (expandRelative r)*
        orbitParameter K false a 1*
        (wordUnit A hs hp E6Base E6Index K (expandRelative r))⁻¹∈
      Positive K⊓rootGroup A hs hp E6Base E6Index K true := ⟨hpositive,hnegative⟩
    rw [positive_inf_negative A hs hp E6Base E6Index coordinateHeight
      (simple_height A hd hs hp ho) K,Subgroup.mem_bot] at hboth
    have he : orbitParameter K false a 1=1 := by
      apply (MulAut.conj (wordUnit A hs hp E6Base E6Index K (expandRelative r))).injective
      change wordUnit A hs hp E6Base E6Index K (expandRelative r)*
          orbitParameter K false a 1*
          (wordUnit A hs hp E6Base E6Index K (expandRelative r))⁻¹=
        wordUnit A hs hp E6Base E6Index K (expandRelative r)*1*
          (wordUnit A hs hp E6Base E6Index K (expandRelative r))⁻¹
      simpa only [mul_one,mul_inv_cancel] using hboth
    exact False.elim (orbitParameter_one_ne_one K a he)
  · exact hneg.1

end SymmetricSubgroupAsymptotics.CFSGE6GeckOrbitOneSignDetection
