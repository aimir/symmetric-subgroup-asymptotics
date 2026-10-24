import SymmetricSubgroupAsymptotics.CFSGFFourBinaryPositiveLeviNormalizer
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWordRootElementSign
import SymmetricSubgroupAsymptotics.CFSGFFourE6RelativeWords

/-! Actual head-zero Weyl parameters normalize the SAME binary radical.
Their root transport is the original signed integral word law; signs
become one in characteristic two. The selected radical-root closure is
proved, rather than supplied as a model-recognition premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourBinaryLeviWeylNormalizer
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGExceptionalCartanPositiveDefinite
open CFSGTwistedE6HeisenbergStableRootFamilies CFSGFFourE6HeisenbergLeviRootClosure
open CFSGFFourE6HeisenbergPositiveLeviClosure CFSGFFourBinaryPositiveLeviNormalizer
open CFSGFFourBinaryFixedRadicalEmbedding CFSGFFourE6DiagramFixed
open CFSGFFourE6PositiveRootUnits CFSGFFourE6RelativeWords
open CFSGNormTwoCoordinateWordRootElementSign CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoCoordinateSelectedRootAdditive CFSGNormTwoCoordinateSelectedRootElement
open CFSGTwistedE6RelativeWeylOrbits CFSGFFourSerreMatrices CFSGSerreQuadraticMatrix
open CFSGSerreQuadraticWeylWord
local instance fFourLeviWeylNormalizerRootsDecidableEq : DecidableEq (Roots CartanMatrix.E₆) :=
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

theorem weyl_conjugate_parameter_mem (K : Type) [Field K] [CharP K 2]
    (b : Label) (i : Fin 5) (t : K) :
    canonicalWeyl e6Data K (leviSimple i) * parameter K b t *
      (canonicalWeyl e6Data K (leviSimple i))⁻¹ ∈ fullHeisenberg K := by
  obtain ⟨c,hc⟩ := reflection_step_closed b i
  have hroot : wordRoot A hs hp (coordinateBase A hd hs hp ho)
      (coordinateIndexEquiv A hd hs hp ho) [leviSimple i] (radicalRoot b) = radicalRoot c := by
    apply Subtype.ext
    change (radicalRoot b).val - integerPairing A (radicalRoot b).val
      (coordinateIndexEquiv A hd hs hp ho (leviSimple i) : Roots A).val •
      (coordinateIndexEquiv A hd hs hp ho (leviSimple i) : Roots A).val = (radicalRoot c).val
    exact hc.symm
  obtain ⟨e,he,htransport⟩ := word_selected_root_sign A hd hs hp ho [leviSimple i] (radicalRoot b)
  have hsign : (e : K)=1 := by
    rcases he with rfl | rfl <;> simp only [Int.cast_one,Int.cast_neg,CharTwo.neg_eq]
  have hconj : canonicalWeyl e6Data K (leviSimple i) * parameter K b t *
      (canonicalWeyl e6Data K (leviSimple i))⁻¹ = parameter K c t := by
    have ht := htransport K t
    rw [hroot,hsign,one_mul] at ht
    simpa only [canonicalWord,mul_one] using ht
  rw [hconj]
  exact selected_parameter_mem K c t

theorem simple_weyl_mem_normalizer (K : Type) [Field K] [Finite K] [CharP K 2]
    (i : Fin 5) :
    canonicalWeyl e6Data K (leviSimple i) ∈ Subgroup.normalizer (fullHeisenberg K : Set (U K)) := by
  letI : Fintype K := Fintype.ofFinite K
  let g : U K := canonicalWeyl e6Data K (leviSimple i)
  have hle : fullHeisenberg K ≤ (fullHeisenberg K).comap (MulAut.conj g).toMonoidHom := by
    calc
      fullHeisenberg K = ⨆ b : Label, (parameterHom K b).range := fullHeisenberg_eq_join K
      _ ≤ (fullHeisenberg K).comap (MulAut.conj g).toMonoidHom := by
        apply iSup_le
        intro b x hx
        obtain ⟨t,rfl⟩ := hx
        change g * parameter K b t.toAdd * g⁻¹ ∈ fullHeisenberg K
        exact weyl_conjugate_parameter_mem K b i t.toAdd
  apply Subgroup.mem_normalizer_fintype
  intro x hx
  exact hle hx

theorem folded_weyl_mem_normalizer (K : Type) [Field K] [Finite K] [CharP K 2]
    (n : Fin 3) : canonicalWeyl realizationData K n.castSucc ∈
      Subgroup.normalizer (fullHeisenberg K : Set (U K)) := by
  rw [foldedWeyl_eq_orbitWord]
  fin_cases n
  · change canonicalWeyl e6Data K 0 * (canonicalWeyl e6Data K 5 * 1) ∈ _
    rw [mul_one]
    exact (Subgroup.normalizer (fullHeisenberg K : Set (U K))).mul_mem
      (simple_weyl_mem_normalizer K 0) (simple_weyl_mem_normalizer K 4)
  · change canonicalWeyl e6Data K 2 * (canonicalWeyl e6Data K 4 * 1) ∈ _
    rw [mul_one]
    exact (Subgroup.normalizer (fullHeisenberg K : Set (U K))).mul_mem
      (simple_weyl_mem_normalizer K 1) (simple_weyl_mem_normalizer K 3)
  · change canonicalWeyl e6Data K 3 * 1 ∈ _
    rw [mul_one]
    exact simple_weyl_mem_normalizer K 2

theorem folded_weyl_mem_radical_normalizer (K : Type) [Field K] [Finite K] [CharP K 2]
    (n : Fin 3) : canonicalWeyl realizationData K n.castSucc ∈
      Subgroup.normalizer ((matrixHom K).range : Set (U K)) := by
  rw [matrixHom_range_eq_inf]
  apply Subgroup.inf_normalizer_le_normalizer_inf
  have hfixed : canonicalWeyl realizationData K n.castSucc ∈ diagramFixed K :=
    (diagramFixed K).mul_mem
      ((diagramFixed K).mul_mem (folded_root_fixed K false n.castSucc 1)
        (folded_root_fixed K true n.castSucc (-1)))
      (folded_root_fixed K false n.castSucc 1)
  exact ⟨folded_weyl_mem_normalizer K n,(diagramFixed K).le_normalizer hfixed⟩

end SymmetricSubgroupAsymptotics.CFSGFFourBinaryLeviWeylNormalizer
