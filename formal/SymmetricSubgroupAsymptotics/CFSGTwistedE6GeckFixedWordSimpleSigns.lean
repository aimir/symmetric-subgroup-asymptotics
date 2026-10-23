import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedSimpleTests
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNegativeSimpleWord
import SymmetricSubgroupAsymptotics.CFSGFixedSubgroupConjugation

/-! Disjointness of the literal fixed positive groups detects opposition
of an actual relative Weyl word. Paired simple roots are tested by their
whole fixed orbit product, rather than by incorrectly fixed individual
root elements. All coefficient automorphisms and characteristics occur. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedWordSimpleSigns
open CFSGTwistedE6GeckFixedSimpleTests CFSGTwistedE6GeckRelativeRootGenerated
open CFSGTwistedE6GeckPositiveTwist CFSGTwistedE6GeckRelativeWordTwist
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckMatrixTwist
open CFSGTwistedE6WeylChamber CFSGTwistedE6RelativeWeylOrbits CFSGTwistedE6FixedWordClassification
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckIntegralWord CFSGNormTwoGeckIntegralRealization
open CFSGNormTwoCoordinateWeylRootMembership CFSGNormTwoCartanDiagramRoots CFSGSerreDiagram
open CFSGNormTwoCartanDiagramWords
open CFSGNormTwoCoordinateNegativeSimpleWord CFSGFixedSubgroupConjugation
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

private theorem source_eq_one_of_disjoint {G : Type*} [Group G]
    (H : Subgroup G) (g x : G) (hx : x∈H) (hgx : g*x*g⁻¹∈H)
    (hdisjoint : H⊓H.map (MulAut.conj g).toMonoidHom=⊥) : x=1 := by
  have hm : g*x*g⁻¹∈H⊓H.map (MulAut.conj g).toMonoidHom := ⟨hgx,⟨x,hx,rfl⟩⟩
  rw [hdisjoint,Subgroup.mem_bot] at hm
  apply (MulAut.conj g).injective
  exact hm.trans (map_one (MulAut.conj g)).symm

theorem positive_simple_partner (w : List (Fin 6))
    (hcomm : ∀k,diagramRoot (rootAction w k)=rootAction w (diagramRoot k))
    (i : Fin 6) (hi : ∀j,0≤(rootAction w (E6Index i)).val j) :
    ∀j,0≤(rootAction w (E6Index (e6Permutation i))).val j := by
  have he : diagramRoot (rootAction w (E6Index i))=
      rootAction w (E6Index (e6Permutation i)) := by
    rw [hcomm]
    exact congrArg (rootAction w)
      (simple_rootPermutation A hd hs hp ho e6Permutation e6_preserves i)
  intro j
  calc
    0≤(rootAction w (E6Index i)).val (e6Permutation.symm j) := hi _
    _=(diagramRoot (rootAction w (E6Index i))).val j := rfl
    _=(rootAction w (E6Index (e6Permutation i))).val j :=
      congrArg (fun k : CFSGNormTwoRootPairing.Roots A=>k.val j) he

theorem positive_conjugate_orbit (K : Type) [Field K] (r : List (Fin 4)) (a : Fin 4)
    (hall : ∀i∈orbitWord a,∀j,0≤(rootAction (expandRelative r) (E6Index i)).val j) :
    (wordUnit A hs hp E6Base E6Index K (expandRelative r))*orbitParameter K false a 1*
      (wordUnit A hs hp E6Base E6Index K (expandRelative r))⁻¹∈Positive K := by
  let W := wordUnit A hs hp E6Base E6Index K (expandRelative r)
  have hi (i : Fin 6) (him : i∈orbitWord a) :
      (MulAut.conj W) (CFSGSerreQuadraticMatrix.canonicalRoot rawData K false i 1)∈Positive K :=
    positive_word_mem A hd hs hp ho K (expandRelative r) i 1 (hall i him)
  change (MulAut.conj W) (orbitParameter K false a 1)∈Positive K
  fin_cases a
  · change (MulAut.conj W)
      (CFSGSerreQuadraticMatrix.canonicalRoot rawData K false 0 1*
        CFSGSerreQuadraticMatrix.canonicalRoot rawData K false 5 1)∈Positive K
    rw [map_mul]
    exact (Positive K).mul_mem (hi 0 (by decide)) (hi 5 (by decide))
  · change (MulAut.conj W)
      (CFSGSerreQuadraticMatrix.canonicalRoot rawData K false 2 1*
        CFSGSerreQuadraticMatrix.canonicalRoot rawData K false 4 1)∈Positive K
    rw [map_mul]
    exact (Positive K).mul_mem (hi 2 (by decide)) (hi 4 (by decide))
  · exact hi 3 (by decide)
  · exact hi 1 (by decide)

theorem relative_simple_nonpositive_of_fixed_disjoint (K : Type) [Field K] (sigma : K≃+*K)
    (r : List (Fin 4))
    (hdisj : signedFixed K sigma false⊓(signedFixed K sigma false).map
      (MulAut.conj (wordUnit A hs hp E6Base E6Index K (expandRelative r))).toMonoidHom=⊥)
    (i : Fin 6) : ∀j,(rootAction (expandRelative r) (E6Index i)).val j≤0 := by
  let W := wordUnit A hs hp E6Base E6Index K (expandRelative r)
  have hW : unitTwist K sigma W=W := by
    change unitTwist K sigma (wordUnit A hs hp E6Base E6Index K (expandRelative r))=
      wordUnit A hs hp E6Base E6Index K (expandRelative r)
    rw [word_eq_canonicalWord]
    exact relative_word_fixed K sigma r
  rcases word_sign_membership A hd hs hp ho K (expandRelative r) i 1 with hpos|hneg
  · obtain ⟨a,ha⟩ := node_orbit_cover i
    have hall : ∀j∈orbitWord a,∀l,0≤(rootAction (expandRelative r) (E6Index j)).val l := by
      intro j hj
      rcases ha j hj with he|he
      · rw [he]
        exact hpos.1
      · rw [he]
        exact positive_simple_partner (expandRelative r) (relative_root_action_commutes r) i hpos.1
    have hx := orbitParameter_one_mem_signedFixed K sigma a
    have hcx : W*orbitParameter K false a 1*W⁻¹∈signedFixed K sigma false := by
      refine ⟨positive_conjugate_orbit K r a hall,?_⟩
      change unitTwist K sigma (W*orbitParameter K false a 1*W⁻¹)=_
      rw [map_mul,map_mul,map_inv,hW,hx.2]
    exact False.elim (orbitParameter_one_ne_one K a
      (source_eq_one_of_disjoint (signedFixed K sigma false) W _ hx hcx hdisj))
  · exact hneg.1

theorem ambient_positive_image_eq_negative_of_fixed_disjoint (K : Type) [Field K] [Finite K]
    (sigma : K≃+*K) (r : List (Fin 4))
    (hdisj : signedFixed K sigma false⊓(signedFixed K sigma false).map
      (MulAut.conj (wordUnit A hs hp E6Base E6Index K (expandRelative r))).toMonoidHom=⊥) :
    (Positive K).map (MulAut.conj
      (wordUnit A hs hp E6Base E6Index K (expandRelative r))).toMonoidHom=Negative K :=
  positive_map_eq_negative_of_simple_nonpositive A hd hs hp ho K (expandRelative r)
    (relative_simple_nonpositive_of_fixed_disjoint K sigma r hdisj)

theorem fixed_positive_image_eq_negative_of_disjoint (K : Type) [Field K] [Finite K]
    (sigma : K≃+*K) (r : List (Fin 4))
    (hdisj : signedFixed K sigma false⊓(signedFixed K sigma false).map
      (MulAut.conj (wordUnit A hs hp E6Base E6Index K (expandRelative r))).toMonoidHom=⊥) :
    (signedFixed K sigma false).map (MulAut.conj
      (wordUnit A hs hp E6Base E6Index K (expandRelative r))).toMonoidHom=signedFixed K sigma true := by
  have hW : unitTwist K sigma (wordUnit A hs hp E6Base E6Index K (expandRelative r))=
      wordUnit A hs hp E6Base E6Index K (expandRelative r) := by
    rw [word_eq_canonicalWord]
    exact relative_word_fixed K sigma r
  change (Positive K⊓CFSGCentralTwistedCommutatorLift.fixedSubgroup (unitTwist K sigma)).map
    (MulAut.conj (wordUnit A hs hp E6Base E6Index K (expandRelative r))).toMonoidHom=_
  rw [map_inf_fixed (unitTwist K sigma) _ _ hW,
    ambient_positive_image_eq_negative_of_fixed_disjoint K sigma r hdisj]
  rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedWordSimpleSigns
