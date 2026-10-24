import SymmetricSubgroupAsymptotics.CFSGFFourE6HeisenbergLeviRootClosure
import SymmetricSubgroupAsymptotics.CFSGExceptionalHeisenbergCharTwoRootRange
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCharTwoSimpleConjugation
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootSubgroupCommute
import SymmetricSubgroupAsymptotics.CFSGFFourE6PositiveRootUnits

/-! Actual positive-Levi conjugation preserves each displayed root
parameter inside the SAME full Heisenberg chart range. The root closure
certificate is paid by checked selected lattice identities; no subgroup
recognition or parabolic membership is supplied as a hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6HeisenbergPositiveLeviClosure
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGTwistedE6HeisenbergStableRootFamilies
open CFSGFFourE6HeisenbergLeviRootClosure CFSGExceptionalHeisenbergProduct
open CFSGExceptionalHeisenbergCharTwoRootRange CFSGNormTwoCoordinateSelectedRootElement
open CFSGNormTwoCoordinateSelectedRootAdditive CFSGNormTwoCoordinateRootSubgroupCommute
open CFSGNormTwoCoordinateRaisedRoot CFSGFFourSerreMatrices CFSGSerreQuadraticMatrix
open CFSGFFourE6PositiveRootUnits
local instance fFourPositiveLeviClosureRootsDecidableEq : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
private abbrev Label := Fin 10 ⊕ (Fin 10 ⊕ Unit)
private abbrev U (K : Type) [CommRing K] := (Matrix Index Index K)ˣ
private abbrev parameterHom (K : Type) [CommRing K] (b : Label) : Multiplicative K →* U K :=
  selectedRootHom A hd hs hp ho K (radicalRoot b)
private abbrev parameter (K : Type) [CommRing K] (b : Label) (t : K) : U K :=
  selectedRootElement A hd hs hp ho K (radicalRoot b) t
private abbrev simple (K : Type) [CommRing K] (j : Fin 6) (a : K) : U K :=
  canonicalRoot e6Data K false j a

def fullHeisenberg (K : Type) [Field K] : Subgroup (U K) :=
  (rawHom A hd hs hp ho configuration K).range

theorem fullHeisenberg_eq_join (K : Type) [Field K] [CharP K 2] :
    fullHeisenberg K = ⨆ b : Label, (parameterHom K b).range := by
  have hroots : rootFamily A configuration = radicalRoot := by
    funext b
    rcases b with b | (b | b) <;> rfl
  simpa only [fullHeisenberg,parameterHom,hroots] using
    rawHom_range_eq_selected_join A hd hs hp ho configuration K

theorem selected_parameter_mem (K : Type) [Field K] [CharP K 2]
    (b : Label) (t : K) : parameter K b t ∈ fullHeisenberg K := by
  rw [fullHeisenberg_eq_join]
  exact (le_iSup (fun c : Label => (parameterHom K c).range) b)
    ⟨Multiplicative.ofAdd t,rfl⟩

private theorem root_positive (b : Label) : ∀ j,0≤(radicalRoot b).val j := by
  rcases b with b | (b | b)
  · exact configuration.positive_x b
  · exact configuration.positive_y b
  · exact configuration.positive_z

private theorem simple_commutes (K : Type) [Field K] (b : Label) (j : Fin 6)
    (hpair : integerPairing A (radicalRoot b).val
      (coordinateIndexEquiv A hd hs hp ho j : Roots A).val=0 ∨
      integerPairing A (radicalRoot b).val
      (coordinateIndexEquiv A hd hs hp ho j : Roots A).val=1) (a t : K) :
    Commute (simple K j a) (parameter K b t) :=
  (rootSubgroup_pair_commute A hd hs hp ho K (radicalRoot b)
    (coordinateIndexEquiv A hd hs hp ho j) hpair _ _
    (selectedRootElement_mem A hd hs hp ho K (radicalRoot b) t)
    (canonicalRoot_mem_rootSubgroup A hd hs hp ho K j a)).symm

theorem positive_conjugate_parameter_mem (K : Type) [Field K] [CharP K 2]
    (b : Label) (i : Fin 5) (a t : K) :
    simple K (leviSimple i) a*parameter K b t*(simple K (leviSimple i) a)⁻¹ ∈
      fullHeisenberg K := by
  rcases positive_step_closed b i with hzero | hone | ⟨hminus,c,hc⟩
  · have hcomm := simple_commutes K b (leviSimple i) (Or.inl hzero) a t
    have hfixed : simple K (leviSimple i) a*parameter K b t*
        (simple K (leviSimple i) a)⁻¹ = parameter K b t := by
      rw [hcomm.eq]
      group
    rw [hfixed]
    exact selected_parameter_mem K b t
  · have hcomm := simple_commutes K b (leviSimple i) (Or.inr hone) a t
    have hfixed : simple K (leviSimple i) a*parameter K b t*
        (simple K (leviSimple i) a)⁻¹ = parameter K b t := by
      rw [hcomm.eq]
      group
    rw [hfixed]
    exact selected_parameter_mem K b t
  · have hroot : raisedRoot A hd hs hp ho (radicalRoot b) (leviSimple i) hminus =
        radicalRoot c := by
      apply Subtype.ext
      exact hc.symm
    have hstep : simple K (leviSimple i) a*parameter K b t*
        (simple K (leviSimple i) a)⁻¹ = parameter K b t*parameter K c (a*t) := by
      have h := CFSGNormTwoCoordinateCharTwoSimpleConjugation.simple_positive_conjugate
        A hd hs hp ho K (radicalRoot b) (root_positive b) (leviSimple i) hminus a t
      rw [hroot] at h
      exact h
    rw [hstep]
    exact (fullHeisenberg K).mul_mem (selected_parameter_mem K b t)
      (selected_parameter_mem K c (a*t))

end SymmetricSubgroupAsymptotics.CFSGFFourE6HeisenbergPositiveLeviClosure
