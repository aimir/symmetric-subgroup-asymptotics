import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootLineNormalizers
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckAmbientPositiveSylow
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNormalizerSoluble
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOppositeNormalizerIntersection
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootIntersection

/-! The actual positive normalizer in the elementary D4 image factors
as U times the simultaneous normalizer of U and V. The second factor
is diagonal. This envelope may exceed the literal generated torus. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckNormalizerEnvelope
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckPositiveTwist CFSGTrialityGeckSourceWordAction
open CFSGTrialityGeckAmbientPositiveSylow CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckIntegralRealization
open CFSGNormTwoGeckBorelEnvelope CFSGNormTwoGeckBorelFactorization
open CFSGNormTwoCoordinateNormalizerWord CFSGNormTwoCoordinateNormalizerDiagonalFactor
open CFSGNormTwoCoordinateNormalizerSoluble CFSGNormTwoCoordinateRootLineNormalizers
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckIntegralWord
open CFSGNormTwoCoordinateOppositeNormalizerIntersection
open CFSGNormTwoCoordinateCanonicalSimpleRootLine CFSGNormTwoCoordinateRootIntersection
local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4

abbrev Negative (K : Type) [Field K] := rootGroup A hs hp Base Index K true

def diagonalNormalizer (K : Type) [Field K] : Subgroup (Matrix GeckIndex GeckIndex K)ˣ :=
  (Subgroup.normalizer (Positive K : Set (Matrix GeckIndex GeckIndex K)ˣ) ⊓
    Subgroup.normalizer (Negative K : Set (Matrix GeckIndex GeckIndex K)ˣ)) ⊓ MatrixGroup K

def normalizerEnvelope (K : Type) [Field K] : Subgroup (Matrix GeckIndex GeckIndex K)ˣ :=
  Subgroup.normalizer (Positive K : Set (Matrix GeckIndex GeckIndex K)ˣ) ⊓ MatrixGroup K

theorem positive_le_envelope (K : Type) [Field K] : Positive K ≤ normalizerEnvelope K :=
  le_inf (Positive K).le_normalizer (positive_le_matrixGroup K)

theorem diagonalNormalizer_le_envelope (K : Type) [Field K] :
    diagonalNormalizer K ≤ normalizerEnvelope K :=
  le_inf (inf_le_left.trans inf_le_left) inf_le_right

theorem normalizer_envelope_factor (K : Type) [Field K]
    (g : (Matrix GeckIndex GeckIndex K)ˣ) (hg : g ∈ normalizerEnvelope K) :
    ∃ u ∈ Positive K, ∃ d ∈ diagonalNormalizer K,
      (d : Matrix GeckIndex GeckIndex K).IsDiag ∧ g = u*d := by
  have hred : ∃ w : List (Fin 4), ∃ b : (Matrix GeckIndex GeckIndex K)ˣ,
      b ∈ borelEnvelope A hs hp Base Index K ∧
      ∃ c : (Matrix GeckIndex GeckIndex K)ˣ,
      c ∈ borelEnvelope A hs hp Base Index K ∧
      g = b * wordUnit A hs hp Base Index K w * c ∧
      wordUnit A hs hp Base Index K w ∈
        Subgroup.normalizer (Positive K : Set (Matrix GeckIndex GeckIndex K)ˣ) ∧
      (∀ i l, 0 ≤ (wordRoot A hs hp Base Index w (Index i)).val l) ∧
      (∀ i l, 0 ≤ (wordRoot A hs hp Base Index
        (CFSGNormTwoGeckWeylWordAlgebra.inverseWord w) (Index i)).val l) :=
    normalizer_word_reduction A hd hs hp ho K g hg.2 hg.1
  obtain ⟨w,b,hb,c,hc,he,hn,_⟩ := hred
  obtain ⟨u,hu,t,ht,hb⟩ := borel_factor A hs hp Base Index K b hb
  obtain ⟨v,hv,s,hs',hc⟩ := borel_factor A hs hp Base Index K c hc
  let n := wordUnit A hs hp Base Index K w
  let NP := Subgroup.normalizer (Positive K : Set (Matrix GeckIndex GeckIndex K)ˣ)
  let NV := Subgroup.normalizer (Negative K : Set (Matrix GeckIndex GeckIndex K)ˣ)
  have hw := normalizer_word_identity K w hn
  have hnV : n ∈ NV := by
    dsimp only [n, NV]
    rw [word_eq_canonicalWord]
    exact identity_word_normalizes A hd hs hp ho K w hw true
  have htP : t ∈ NP := torusGroup_normalizes A hd hs hp ho K false ht
  have hsP : s ∈ NP := torusGroup_normalizes A hd hs hp ho K false hs'
  have htV : t ∈ NV := torusGroup_normalizes A hd hs hp ho K true ht
  have hsV : s ∈ NV := torusGroup_normalizes A hd hs hp ho K true hs'
  have htn : t*n ∈ NP := NP.mul_mem htP hn
  have hv' : (t*n)*v*(t*n)⁻¹ ∈ Positive K :=
    (Subgroup.mem_normalizer_iff.mp htn v).mp hv
  have hdP : (t*n)*s ∈ NP := NP.mul_mem htn hsP
  have hdV : (t*n)*s ∈ NV := NV.mul_mem (NV.mul_mem htV hnV) hsV
  have hdH : (t*n)*s ∈ MatrixGroup K :=
    (MatrixGroup K).mul_mem ((MatrixGroup K).mul_mem
      (torusGroup_le_canonical A hs hp Base Index K ht)
      (wordUnit_mem_canonical A hd hs hp ho K w))
      (torusGroup_le_canonical A hs hp Base Index K hs')
  refine ⟨u*((t*n)*v*(t*n)⁻¹),(Positive K).mul_mem hu hv',
    (t*n)*s,⟨⟨hdP,hdV⟩,hdH⟩,?_,?_⟩
  · have hdn := word_isDiag_of_linear_identity A hd hs hp ho K
      cartanSign cartanSign_square cartanSign_pairing w hw
    change (wordUnit A hs hp Base Index K w : Matrix GeckIndex GeckIndex K).IsDiag at hdn
    obtain ⟨dt,hdt⟩ := torus_diagonal_of_mem A hs hp Base Index K t ht
    obtain ⟨ds,hds⟩ := torus_diagonal_of_mem A hs hp Base Index K s hs'
    change Matrix.IsDiag ((t : Matrix GeckIndex GeckIndex K)*
      (n : Matrix GeckIndex GeckIndex K)*(s : Matrix GeckIndex GeckIndex K))
    dsimp only [n]
    rw [hdt,hds,←hdn.diagonal_diag,Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]
    exact Matrix.isDiag_diagonal _
  · rw [he,hb,hc]
    dsimp only [n]
    group

theorem positive_mem_negative_normalizer_eq_one (K : Type) [Field K]
    (u : (Matrix GeckIndex GeckIndex K)ˣ) (hu : u ∈ Positive K)
    (hn : u ∈ Subgroup.normalizer (Negative K : Set (Matrix GeckIndex GeckIndex K)ˣ)) :
    u = 1 := by
  have hroot (i : Fin 4) : u ∈ canonicalRootSubgroup rawData K false i := by
    have hmem : u ∈ rootGroup A hs hp Base Index K false ⊓
        ((Subgroup.normalizer (rootGroup A hs hp Base Index K true : Set _) ⊓
          canonicalElementaryGroup rawData K) ⊔ canonicalRootSubgroup rawData K false i) :=
      ⟨hu,(show Subgroup.normalizer (rootGroup A hs hp Base Index K true : Set _) ⊓
        canonicalElementaryGroup rawData K ≤ _ from le_sup_left)
          ⟨hn,positive_le_matrixGroup K hu⟩⟩
    have heq : rootGroup A hs hp Base Index K false ⊓
        ((Subgroup.normalizer (rootGroup A hs hp Base Index K true : Set _) ⊓
          canonicalElementaryGroup rawData K) ⊔ canonicalRootSubgroup rawData K false i) =
        canonicalRootSubgroup rawData K false i :=
      opposite_normalizer_parabolic_intersection A hd hs hp ho K
        cartanSign cartanSign_square cartanSign_pairing (normalizer_word_identity K) i
    rwa [heq] at hmem
  have hzero := hroot 0
  have hone := hroot 1
  have hsimple (i : Fin 4) :
      CFSGNormTwoCoordinateRootSubgroup.rootSubgroup A hd hs hp ho K (Index i) =
        canonicalRootSubgroup rawData K false i :=
    rootSubgroup_simple_eq_canonical A hd hs hp ho K i
  rw [←hsimple 0] at hzero
  rw [←hsimple 1] at hone
  exact eq_one_of_mem_two_roots A hd hs hp ho K (Index 0) (Index 1)
    (by
      intro h
      have hi : Index 0 = Index 1 := Subtype.ext h
      exact (by decide : (0 : Fin 4) ≠ 1) (Index.injective hi)) u hzero hone

theorem diagonalNormalizer_isDiag (K : Type) [Field K]
    (g : (Matrix GeckIndex GeckIndex K)ˣ) (hg : g ∈ diagonalNormalizer K) :
    (g : Matrix GeckIndex GeckIndex K).IsDiag := by
  obtain ⟨u,hu,d,hdD,hdiag,he⟩ := normalizer_envelope_factor K g
    (diagonalNormalizer_le_envelope K hg)
  have huV : u ∈ Subgroup.normalizer (Negative K : Set (Matrix GeckIndex GeckIndex K)ˣ) := by
    have hh := (Subgroup.normalizer (Negative K : Set (Matrix GeckIndex GeckIndex K)ˣ)).mul_mem
      hg.1.2 ((Subgroup.normalizer (Negative K : Set (Matrix GeckIndex GeckIndex K)ˣ)).inv_mem hdD.1.2)
    rw [he,mul_inv_cancel_right] at hh
    exact hh
  have hu1 := positive_mem_negative_normalizer_eq_one K u hu huV
  rw [hu1,one_mul] at he
  rw [he]
  exact hdiag

theorem diagonalNormalizer_commute (K : Type) [Field K]
    (g h : diagonalNormalizer K) : Commute g h := by
  change g*h = h*g
  apply Subtype.ext
  apply Units.ext
  have hg := diagonalNormalizer_isDiag K g.val g.property
  have hh := diagonalNormalizer_isDiag K h.val h.property
  change (g.val : Matrix GeckIndex GeckIndex K)*(h.val : Matrix GeckIndex GeckIndex K) =
    (h.val : Matrix GeckIndex GeckIndex K)*(g.val : Matrix GeckIndex GeckIndex K)
  rw [←hg.diagonal_diag,←hh.diagonal_diag,Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]
  congr 1
  exact mul_comm _ _

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckNormalizerEnvelope
