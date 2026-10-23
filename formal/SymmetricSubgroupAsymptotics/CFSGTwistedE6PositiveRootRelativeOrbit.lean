import SymmetricSubgroupAsymptotics.CFSGTwistedE6PositiveOrbitStep
import SymmetricSubgroupAsymptotics.CFSGTwistedE6FixedWordClassification

/-! Actual relative reflection words reduce every positive E6 root to
a simple root. The word is constructed by strong induction on integer
coordinate height using the proved positive orbit step. No relative-root
coverage or finite Weyl table is supplied as a premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6PositiveRootRelativeOrbit
open CFSGTwistedE6PositiveOrbitStep CFSGTwistedE6WeylChamber
open CFSGTwistedE6RelativeWeylOrbits CFSGTwistedE6FixedWordClassification
open CFSGNormTwoRootPairing CFSGExceptionalNormTwoBases CFSGIntegerHeightSign

theorem exists_relative_word_simple (k : Roots CartanMatrix.E₆) (hk : ∀i,0≤k.val i) :
    ∃(r : List (Fin 4)) (j : Fin 6),rootAction (expandRelative r) k=(E6Index j:Roots CartanMatrix.E₆) := by
  have H : ∀m : ℕ,∀k : Roots CartanMatrix.E₆,(height k.val).toNat=m→
      (∀i,0≤k.val i)→∃(r : List (Fin 4)) (j : Fin 6),
        rootAction (expandRelative r) k=(E6Index j:Roots CartanMatrix.E₆) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih=>
      intro k hm hk
      by_cases hsimple : ∃j,k=(E6Index j:Roots CartanMatrix.E₆)
      · obtain ⟨j,hj⟩ := hsimple
        exact ⟨[],j,hj⟩
      have hns : ∀i,k≠(E6Index i:Roots CartanMatrix.E₆) := fun i he=>hsimple ⟨i,he⟩
      obtain ⟨a,hpositive,hheight⟩ := positive_orbit_step k hk hns
      let k' := rootAction (orbitWord a) k
      have hnonneg : 0≤height k.val := Finset.sum_nonneg (fun i _=>hk i)
      have hnonneg' : 0≤height k'.val := Finset.sum_nonneg (fun i _=>hpositive i)
      have hlt : (height k'.val).toNat<m := by
        change height k'.val<height k.val at hheight
        omega
      obtain ⟨r,j,hr⟩ := ih (height k'.val).toNat hlt k' rfl hpositive
      refine ⟨r++[a],j,?_⟩
      rw [expandRelative_append]
      simp only [expandRelative,List.append_nil]
      rw [CFSGTwistedE6FixedWordClassification.rootAction_append]
      exact hr
  exact H (height k.val).toNat k rfl hk

end SymmetricSubgroupAsymptotics.CFSGTwistedE6PositiveRootRelativeOrbit
