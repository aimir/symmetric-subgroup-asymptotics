import SymmetricSubgroupAsymptotics.CFSGReeFFourPositiveHeightTorus
import SymmetricSubgroupAsymptotics.CFSGFiniteOddOrbitCoordinateExtraction
import SymmetricSubgroupAsymptotics.CFSGFiniteDiagonalCharacterAverage
import Mathlib.Algebra.CharP.Two

/-! Each coordinate of the full positive subgroup can be matched by a
literal product of torus commutators in the same height tail. Nontrivial
characters and the odd torus cardinality are used only for m>0. No fixed
coordinate lifting or generation by simple root groups is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourPositiveDerivedCoordinates
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourPositiveHeightCoordinates
open CFSGReeFFourPositiveHeightTorus CFSGNormTwoCoordinateExactHeightLayer
local notation "A" => CartanMatrix.E₆
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _

theorem exists_derived_same_coordinate (m : ℕ) (hm : 0<m)
    (h : ℤ) (hh : 0<h) (u : tail m h) :
    ∃v : tail m h, (v.val : originalModelFixed m)∈commutator (originalModelFixed m) ∧
      coordinateHom m h hh v=coordinateHom m h hh u := by
  let T := (Field m)ˣ×(Field m)ˣ
  letI : Fintype T := Fintype.ofFinite T
  let S : Subgroup (tail m h) := (commutator (originalModelFixed m)).comap
    ((fixedPositive m).subtype.comp (tail m h).subtype)
  let phi := coordinateHom m h hh
  let c : T→tail m h := fun t=>torusConjugate m h t u
  have htwo : ∀v : ExactHeightRoot A h→Field m,v+v=0 := by
    intro v
    funext k
    exact CharTwo.add_self_eq_zero (v k)
  have hodd : Odd (Fintype.card T) := by
    simpa only [Nat.card_eq_fintype_card] using
      CFSGReeFFourRootTorusCharacters.torus_parameter_card_odd m
  have horbit : ∑t : T,(phi (c t)).toAdd=0 := by
    calc
      _ = ∑t : T,fun k : ExactHeightRoot A h=>
          (CFSGReeFFourRootTorusCharacters.rootCharacter m k.val.val t : Field m)*
            (phi u).toAdd k := by
        apply Finset.sum_congr rfl
        intro t _
        funext k
        exact torusConjugate_coordinate m h hh t u k
      _ = 0 := CFSGFiniteDiagonalCharacterAverage.diagonal_orbit_sum_eq_zero
        (fun k : ExactHeightRoot A h=>
          CFSGReeFFourRootTorusCharacters.rootCharacter m k.val.val)
        (fun k=>CFSGReeFFourRootTorusCharacters.rootCharacter_nontrivial m hm k.val.val)
        (phi u).toAdd
  have hcomm : ∀t : T,c t*u⁻¹∈S := by
    intro t
    exact torus_commutator_mem m h t u
  obtain ⟨v,hv,he⟩ := CFSGFiniteOddOrbitCoordinateExtraction.exists_mem_same_coordinate
    S phi c u htwo hodd horbit hcomm
  exact ⟨v,hv,he⟩

end SymmetricSubgroupAsymptotics.CFSGReeFFourPositiveDerivedCoordinates
