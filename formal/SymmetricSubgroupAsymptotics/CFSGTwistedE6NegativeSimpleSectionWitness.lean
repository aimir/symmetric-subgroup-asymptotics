import SymmetricSubgroupAsymptotics.CFSGTwistedE6PositiveRootRelativeOrbit
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLatticeWord

/-! Every positive E6 root has a relative-word witness based at a
NEGATIVE simple root. This orientation matches the literal root-word
parameter charts used by the checked integral normal form, and keeps
all source conjugators in the original fixed relative subgroup. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6NegativeSimpleSectionWitness
open CFSGTwistedE6PositiveRootRelativeOrbit CFSGTwistedE6WeylChamber
open CFSGTwistedE6RelativeWeylOrbits CFSGTwistedE6FixedWordClassification
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite CFSGNormTwoRootPairing
open CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoGeckWeylWordAlgebra CFSGNormTwoGeckIntegralRealization
open CFSGNormTwoGeckColumns CFSGNormTwoCoordinateLatticeWord

def nodeOrbit (j : Fin 6) : Fin 4 := ![0,3,1,2,1,0] j

theorem orbit_simple_negative (j : Fin 6) :
    rootAction (orbitWord (nodeOrbit j)) (E6Index j)=
      negativeIndex CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite (E6Index j) := by
  have hfinite : ∀i : Fin 6,
      CFSGSignedCartanReflections.latticeWord CartanMatrix.E₆ (orbitWord (nodeOrbit i))*ᵥ
        (Pi.single i (1:ℤ) : Fin 6→ℤ)= -(Pi.single i (1:ℤ) : Fin 6→ℤ) := by decide
  have hlin : CFSGSignedCartanReflections.latticeWord CartanMatrix.E₆ (orbitWord (nodeOrbit j))*ᵥ
      (Pi.single j (1:ℤ) : Fin 6→ℤ)=linearAction (orbitWord (nodeOrbit j)) (Pi.single j 1) :=
    LinearMap.congr_fun (latticeWord_linear CartanMatrix.E₆ CartanMatrix.E₆_diag
      CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos
      (orbitWord (nodeOrbit j))) _
  apply Subtype.ext
  rw [←wordLinear_root,negative_val]
  exact hlin.symm.trans (hfinite j)

theorem exists_relative_word_negative_simple (k : Roots CartanMatrix.E₆) (hk : ∀i,0 ≤ k.val i) :
    ∃(r : List (Fin 4)) (j : Fin 6),rootAction (expandRelative r) k=
      negativeIndex CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite (E6Index j) := by
  obtain ⟨r,j,hr⟩ := exists_relative_word_simple k hk
  refine ⟨nodeOrbit j::r,j,?_⟩
  change rootAction (orbitWord (nodeOrbit j)++expandRelative r) k=_
  rw [CFSGTwistedE6FixedWordClassification.rootAction_append,hr,orbit_simple_negative]

theorem exists_relative_inverse_negative_degree (k : Roots CartanMatrix.E₆) (hk : ∀i,0 ≤ k.val i) :
    ∃(r : List (Fin 4)) (j : Fin 6),
      wordLinear CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index
        (inverseWord (expandRelative r)) (-(E6Index j:Roots CartanMatrix.E₆).val)=k.val := by
  obtain ⟨r,j,hr⟩ := exists_relative_word_negative_simple k hk
  refine ⟨r,j,?_⟩
  have hl : linearAction (expandRelative r) k.val= -(E6Index j:Roots CartanMatrix.E₆).val := by
    rw [wordLinear_root]
    change (rootAction (expandRelative r) k).val= -(E6Index j:Roots CartanMatrix.E₆).val
    rw [hr,negative_val]
  rw [wordLinear_inverseWord,←hl]
  exact (linearAction (expandRelative r)).symm_apply_apply k.val

end SymmetricSubgroupAsymptotics.CFSGTwistedE6NegativeSimpleSectionWitness
