import SymmetricSubgroupAsymptotics.CFSGFFourE6HeisenbergPositiveLeviClosure
import SymmetricSubgroupAsymptotics.CFSGFFourBinaryFixedRadicalRange
import SymmetricSubgroupAsymptotics.CFSGFFourE6DiagramFixed
import Mathlib.Algebra.Group.Subgroup.Finite

/-! The actual positive Levi parameters normalize the SAME full root
chart and its actual diagram-fixed radical. Fixed-coordinate coverage
pays the intersection equality; no parabolic recognition or splitting is
an input. Finiteness is used only to upgrade one-sided conjugation closure. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourBinaryPositiveLeviNormalizer
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGExceptionalCartanPositiveDefinite
open CFSGTwistedE6HeisenbergStableRootFamilies CFSGFFourE6HeisenbergLeviRootClosure
open CFSGFFourE6HeisenbergPositiveLeviClosure CFSGExceptionalHeisenbergProduct
open CFSGFFourBinaryFixedRadicalEmbedding CFSGFFourBinaryFixedRadicalRange
open CFSGFFourE6DiagramFixed CFSGFFourE6PositiveRootUnits
open CFSGTwistedE6HeisenbergCoordinateTwist CFSGTwistedE6GeckMatrixTwist
open CFSGFFourSerreMatrices CFSGSerreQuadraticMatrix
open CFSGNormTwoCoordinateSelectedRootAdditive CFSGNormTwoCoordinateSelectedRootElement
local instance fFourPositiveNormalizerRootsDecidableEq : DecidableEq (Roots CartanMatrix.E₆) :=
  Classical.decEq _
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
private abbrev U (K : Type) [CommRing K] := (Matrix Index Index K)ˣ
private abbrev Label := Fin 10 ⊕ (Fin 10 ⊕ Unit)
private abbrev parameter (K : Type) [CommRing K] (b : Label) (t : K) : U K :=
  selectedRootElement A hd hs hp ho K (radicalRoot b) t
private abbrev parameterHom (K : Type) [CommRing K] (b : Label) : Multiplicative K →* U K :=
  selectedRootHom A hd hs hp ho K (radicalRoot b)

theorem simple_positive_mem_normalizer (K : Type) [Field K] [Finite K] [CharP K 2]
    (i : Fin 5) (a : K) :
    canonicalRoot e6Data K false (leviSimple i) a ∈ (Subgroup.normalizer (fullHeisenberg K : Set (U K))) := by
  letI : Fintype K := Fintype.ofFinite K
  let g : U K := canonicalRoot e6Data K false (leviSimple i) a
  have hle : fullHeisenberg K ≤
      (fullHeisenberg K).comap (MulAut.conj g).toMonoidHom := by
    calc
      fullHeisenberg K = ⨆ b : Label, (parameterHom K b).range := fullHeisenberg_eq_join K
      _ ≤ (fullHeisenberg K).comap (MulAut.conj g).toMonoidHom := by
        apply iSup_le
        intro b x hx
        obtain ⟨t,rfl⟩ := hx
        change g * parameter K b t.toAdd * g⁻¹ ∈
          fullHeisenberg K
        exact positive_conjugate_parameter_mem K b i a t.toAdd
  apply Subgroup.mem_normalizer_fintype
  intro x hx
  exact hle hx

theorem folded_positive_mem_normalizer (K : Type) [Field K] [Finite K] [CharP K 2]
    (n : Fin 3) (a : K) :
    canonicalRoot realizationData K false n.castSucc a ∈ (Subgroup.normalizer (fullHeisenberg K : Set (U K))) := by
  rw [folded_positive_root]
  fin_cases n
  · exact (Subgroup.normalizer (fullHeisenberg K : Set (U K))).mul_mem
      (simple_positive_mem_normalizer K 0 a) (simple_positive_mem_normalizer K 4 a)
  · exact (Subgroup.normalizer (fullHeisenberg K : Set (U K))).mul_mem
      (simple_positive_mem_normalizer K 1 a) (simple_positive_mem_normalizer K 3 a)
  · exact simple_positive_mem_normalizer K 2 a

theorem matrixHom_range_eq_inf (K : Type) [Field K] [CharP K 2] :
    (matrixHom K).range = fullHeisenberg K ⊓ diagramFixed K := by
  ext x
  constructor
  · rintro ⟨g,rfl⟩
    exact ⟨⟨coordinateHom K g,rfl⟩,matrixHom_fixed K g⟩
  · rintro ⟨hx,hfixed⟩
    obtain ⟨g,hg⟩ := hx
    have hfix : unitTwist K (RingEquiv.refl K)
        (rawHom A hd hs hp ho configuration K g) = rawHom A hd hs hp ho configuration K g := by
      rw [hg]
      exact hfixed
    have hcoord := (rawHom_fixed_iff K (RingEquiv.refl K) g).mp hfix
    obtain ⟨v,hv⟩ := (mem_coordinateHom_range_iff_fixed K g).mpr hcoord
    refine ⟨v,?_⟩
    change rawHom A hd hs hp ho configuration K (coordinateHom K v)=x
    rw [hv]
    exact hg

theorem folded_positive_mem_radical_normalizer (K : Type) [Field K] [Finite K] [CharP K 2]
    (n : Fin 3) (a : K) :
    canonicalRoot realizationData K false n.castSucc a ∈ Subgroup.normalizer ((matrixHom K).range : Set (U K)) := by
  rw [matrixHom_range_eq_inf]
  apply Subgroup.inf_normalizer_le_normalizer_inf
  exact ⟨folded_positive_mem_normalizer K n a,
    (diagramFixed K).le_normalizer (folded_root_fixed K false n.castSucc a)⟩

end SymmetricSubgroupAsymptotics.CFSGFFourBinaryPositiveLeviNormalizer
