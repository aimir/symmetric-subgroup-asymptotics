import SymmetricSubgroupAsymptotics.CFSGTwistedE6RelativeWeylOrbits

/-! Every literal E6 Weyl action commuting with the pinned diagram
involution is the action of an actual word in the four folded orbit
reflections. Strong induction uses the finite positive-root inversion
count; no 1152-element Weyl table or recognition premise occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6FixedWordClassification
open CFSGTwistedE6WeylChamber CFSGTwistedE6RelativeWeylOrbits
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite CFSGNormTwoRootPairing
open CFSGNormTwoGeckWeylWordAlgebra CFSGNormTwoGeckWeylLatticeLinear

def expandRelative : List (Fin 4)→List (Fin 6)
  | []=>[]
  | a::r=>orbitWord a++expandRelative r

theorem expandRelative_append (r s : List (Fin 4)) :
    expandRelative (r++s)=expandRelative r++expandRelative s := by
  induction r with
  | nil=>rfl
  | cons a r ih=>simp only [List.cons_append,expandRelative,ih,List.append_assoc]

theorem rootAction_append (v w : List (Fin 6)) (k : Roots CartanMatrix.E₆) :
    rootAction (v++w) k=rootAction v (rootAction w k) :=
  wordRoot_append CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index v w k

theorem linearAction_append (v w : List (Fin 6)) :
    linearAction (v++w)=linearAction v*linearAction w :=
  wordLinear_append CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index v w

theorem relative_root_action_commutes (r : List (Fin 4)) :
    ∀k,diagramRoot (rootAction (expandRelative r) k)=rootAction (expandRelative r) (diagramRoot k) := by
  induction r with
  | nil=>intro k;rfl
  | cons a r ih=>
    intro k
    change diagramRoot (rootAction (orbitWord a++expandRelative r) k)=_
    rw [rootAction_append,orbit_root_commutes,ih]
    exact (rootAction_append (orbitWord a) (expandRelative r) (diagramRoot k)).symm

abbrev wordInversions := CFSGNormTwoCoordinateInversionCount.inversionCount
  CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
  E6_positive_definite CartanMatrix.E₆_off_diag_nonpos

theorem exists_relative_word_action (w : List (Fin 6))
    (hcomm : ∀k,diagramRoot (rootAction w k)=rootAction w (diagramRoot k)) :
    ∃r : List (Fin 4),linearAction w=linearAction (expandRelative r) := by
  suffices ∀n : ℕ,∀v : List (Fin 6),wordInversions v=n→
      (∀k,diagramRoot (rootAction v k)=rootAction v (diagramRoot k))→
        ∃r : List (Fin 4),linearAction v=linearAction (expandRelative r) by
    exact this (wordInversions w) w rfl hcomm
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih=>
    intro v hn hvcomm
    by_cases hv : linearAction v=1
    · exact ⟨[],hv⟩
    obtain ⟨a,ha⟩ := exists_negative_orbit v hv hvcomm
    let v' := v++orbitWord a
    have hv'comm : ∀k,diagramRoot (rootAction v' k)=rootAction v' (diagramRoot k) := by
      intro k
      change diagramRoot (rootAction (v++orbitWord a) k)=rootAction (v++orbitWord a) (diagramRoot k)
      rw [rootAction_append,rootAction_append,hvcomm,orbit_root_commutes]
    have hlt : wordInversions v'<n := by
      have hdrop := negative_orbit_count_drop v a ha
      have hlength := orbitWord_nonempty a
      change wordInversions (v++orbitWord a)+(orbitWord a).length=wordInversions v at hdrop
      change wordInversions (v++orbitWord a)<n
      omega
    obtain ⟨r,hr⟩ := ih (wordInversions v') hlt v' rfl hv'comm
    refine ⟨r++[a],?_⟩
    have hfactor : linearAction v=linearAction v'*linearAction (orbitWord a) := by
      change linearAction v=linearAction (v++orbitWord a)*linearAction (orbitWord a)
      rw [linearAction_append,mul_assoc,orbit_linear_square,mul_one]
    rw [hfactor,hr,expandRelative_append,linearAction_append]
    change linearAction (expandRelative r)*linearAction (orbitWord a)=
      linearAction (expandRelative r)*linearAction (orbitWord a++[])
    rw [List.append_nil]

end SymmetricSubgroupAsymptotics.CFSGTwistedE6FixedWordClassification
