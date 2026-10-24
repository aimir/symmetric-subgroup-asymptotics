import SymmetricSubgroupAsymptotics.CFSGNonpositiveCoordinateCone
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWordDescent
import SymmetricSubgroupAsymptotics.CFSGReeFFourPairedDescentPrefixes
import SymmetricSubgroupAsymptotics.CFSGTwistedE6FixedWordClassification
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLatticeWord

/-! Negativity on the three indicated simple roots gives an actual
three- or six-step inversion drop. Each intermediate root is handled
by its certified nonnegative integer coordinates, before field reduction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourPairedInversionDescent
open CFSGNonpositiveCoordinateCone CFSGReeFFourPairedDescentPrefixes
open CFSGNormTwoCoordinateWordDescent CFSGTwistedE6WeylChamber
open CFSGTwistedE6FixedWordClassification CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoCoordinateLatticeWord CFSGNormTwoGeckWeylWordAlgebra
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

private theorem prefixVector_root (middle : Bool) (n : Fin (pairedWord middle).length) :
    prefixVector middle n=
      (rootAction ((pairedWord middle).take n.val) (E6Index ((pairedWord middle).get n))).val := by
  have h := LinearMap.congr_fun
    (latticeWord_linear A hd hs hp ho ((pairedWord middle).take n.val))
    (Pi.single ((pairedWord middle).get n) (1:ℤ))
  change prefixVector middle n=
    linearAction ((pairedWord middle).take n.val)
      (Pi.single ((pairedWord middle).get n) (1:ℤ)) at h
  exact h.trans (wordLinear_root A hs hp E6Base E6Index
    ((pairedWord middle).take n.val) (E6Index ((pairedWord middle).get n)))

theorem paired_prefix_negative (w : List (Fin 6)) (middle : Bool)
    (hneg : ∀i∈pairedSupport middle,∀j,(rootAction w (E6Index i)).val j≤0)
    (n : Fin (pairedWord middle).length) :
    ∀j,(rootAction (w++(pairedWord middle).take n.val)
      (E6Index ((pairedWord middle).get n))).val j≤0 := by
  have hcolumns : ∀i,prefixVector middle n i≠0→
      ∀j,linearAction w (Pi.single i 1) j≤0 := by
    intro i hi
    have him : i∈pairedSupport middle := by
      by_contra hnot
      exact hi (paired_prefix_supported middle n i hnot)
    have h := hneg i him
    rw [←wordLinear_root A hs hp E6Base E6Index w (E6Index i)] at h
    exact h
  have h := linearMap_nonpositive_of_support_columns (linearAction w).toLinearMap
    (prefixVector middle n) (paired_prefix_nonnegative middle n) hcolumns
  rw [prefixVector_root] at h
  change ∀j,linearAction w
    (rootAction ((pairedWord middle).take n.val) (E6Index ((pairedWord middle).get n))).val j≤0 at h
  rw [wordLinear_root A hs hp E6Base E6Index w] at h
  intro j
  rw [rootAction_append]
  exact h j

theorem paired_inversion_drop (w : List (Fin 6)) (middle : Bool)
    (hneg : ∀i∈pairedSupport middle,∀j,(rootAction w (E6Index i)).val j≤0) :
    wordInversions (w++pairedWord middle)+(pairedWord middle).length=wordInversions w := by
  apply inversionCount_append_of_prefix_negative A hd hs hp ho
  intro u i t he
  have hn : u.length<(pairedWord middle).length := by
    rw [he,List.length_append,List.length_cons]
    omega
  let n : Fin (pairedWord middle).length := ⟨u.length,hn⟩
  have htake : (pairedWord middle).take n.val=u := by
    change (pairedWord middle).take u.length=u
    rw [he]
    exact List.take_left
  have hget : (pairedWord middle).get n=i := by
    change (pairedWord middle)[u.length]=i
    simp [he,List.getElem_append_right]
  have h := paired_prefix_negative w middle hneg n
  rw [htake,hget] at h
  exact h

end SymmetricSubgroupAsymptotics.CFSGReeFFourPairedInversionDescent
