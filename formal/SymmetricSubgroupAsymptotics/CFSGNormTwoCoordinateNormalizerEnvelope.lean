import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootLineNormalizers
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNormalizerSoluble
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOppositeNormalizerIntersection
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootIntersection
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateBruhatBlockUniqueness

/-! The positive normalizer in an actual coordinate elementary group factors
as its positive group times the simultaneous positive/opposite normalizer.
The latter is diagonal, and the entire envelope is triangular in the actual
root/Cartan blocks. The only Weyl input is the literal lattice-identity theorem
for normalizing words, to be discharged in each root system. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNormalizerEnvelope
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckIntegralRealization
open CFSGNormTwoGeckBorelEnvelope CFSGNormTwoGeckBorelFactorization
open CFSGNormTwoCoordinateNormalizerWord CFSGNormTwoCoordinateNormalizerDiagonalFactor
open CFSGNormTwoCoordinateNormalizerSoluble CFSGNormTwoCoordinateRootLineNormalizers
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckIntegralWord
open CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoCoordinateOppositeNormalizerIntersection
open CFSGNormTwoCoordinateCanonicalSimpleRootLine CFSGNormTwoCoordinateRootIntersection
open CFSGNormTwoCoordinateWeylBlocks CFSGNormTwoCoordinateBruhatBlockUniqueness
open CFSGNormTwoRootSeparatingWeight
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀j,A j j=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "J₀" => GeckIndex A hd hs hp ho
local notation "D₀" => realizationData A hs hp b₀ s₀

abbrev Positive (K : Type) [Field K] := rootGroup A hs hp b₀ s₀ K false
abbrev Negative (K : Type) [Field K] := rootGroup A hs hp b₀ s₀ K true
abbrev Elementary (K : Type) [Field K] := canonicalElementaryGroup D₀ K

def diagonalNormalizer (K : Type) [Field K] : Subgroup (Matrix J₀ J₀ K)ˣ :=
  (Subgroup.normalizer (Positive A hd hs hp ho K : Set (Matrix J₀ J₀ K)ˣ) ⊓
    Subgroup.normalizer (Negative A hd hs hp ho K : Set (Matrix J₀ J₀ K)ˣ)) ⊓
      Elementary A hd hs hp ho K

def normalizerEnvelope (K : Type) [Field K] : Subgroup (Matrix J₀ J₀ K)ˣ :=
  Subgroup.normalizer (Positive A hd hs hp ho K : Set (Matrix J₀ J₀ K)ˣ) ⊓
    Elementary A hd hs hp ho K

theorem positive_le_elementary (K : Type) [Field K] :
    Positive A hd hs hp ho K ≤ Elementary A hd hs hp ho K := by
  change rootGroup A hs hp b₀ s₀ K false ≤ canonicalElementaryGroup D₀ K
  rw [←positive_sup_negative A hs hp b₀ s₀ K]
  exact le_sup_left

theorem positive_le_envelope (K : Type) [Field K] :
    Positive A hd hs hp ho K ≤ normalizerEnvelope A hd hs hp ho K :=
  le_inf (Positive A hd hs hp ho K).le_normalizer (positive_le_elementary A hd hs hp ho K)

theorem diagonalNormalizer_le_envelope (K : Type) [Field K] :
    diagonalNormalizer A hd hs hp ho K ≤ normalizerEnvelope A hd hs hp ho K :=
  le_inf (inf_le_left.trans inf_le_left) inf_le_right

variable (K : Type) [Field K]
    (ε : Fin r→ℤ) (hε : ∀i,ε i*ε i=1)
    (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (hidentity : ∀w : List (Fin r),wordUnit A hs hp
      (coordinateBase A hd hs hp ho) (coordinateIndexEquiv A hd hs hp ho) K w∈
      Subgroup.normalizer (Positive A hd hs hp ho K : Set _)→
      wordLinear A hs hp (coordinateBase A hd hs hp ho)
        (coordinateIndexEquiv A hd hs hp ho) w=1)

include ε hε hA hidentity

theorem normalizer_envelope_factor
    (g : (Matrix J₀ J₀ K)ˣ) (hg : g ∈ normalizerEnvelope A hd hs hp ho K) :
    ∃ u ∈ Positive A hd hs hp ho K, ∃ d ∈ diagonalNormalizer A hd hs hp ho K,
      (d : Matrix J₀ J₀ K).IsDiag ∧ g = u*d := by
  obtain ⟨w,b,hb,c,hc,he,hn,_⟩ := normalizer_word_reduction A hd hs hp ho K g hg.2 hg.1
  obtain ⟨u,hu,t,ht,hb⟩ := borel_factor A hs hp b₀ s₀ K b hb
  obtain ⟨v,hv,s,hs',hc⟩ := borel_factor A hs hp b₀ s₀ K c hc
  let n := wordUnit A hs hp b₀ s₀ K w
  let NP := Subgroup.normalizer (Positive A hd hs hp ho K : Set (Matrix J₀ J₀ K)ˣ)
  let NV := Subgroup.normalizer (Negative A hd hs hp ho K : Set (Matrix J₀ J₀ K)ˣ)
  have hw := hidentity w hn
  have hnV : n ∈ NV := by
    dsimp only [n, NV, Negative]
    rw [word_eq_canonicalWord]
    exact identity_word_normalizes A hd hs hp ho K w hw true
  have htP : t ∈ NP := torusGroup_normalizes A hd hs hp ho K false ht
  have hsP : s ∈ NP := torusGroup_normalizes A hd hs hp ho K false hs'
  have htV : t ∈ NV := torusGroup_normalizes A hd hs hp ho K true ht
  have hsV : s ∈ NV := torusGroup_normalizes A hd hs hp ho K true hs'
  have htn : t*n ∈ NP := NP.mul_mem htP hn
  have hv' : (t*n)*v*(t*n)⁻¹ ∈ Positive A hd hs hp ho K :=
    (Subgroup.mem_normalizer_iff.mp htn v).mp hv
  have hdP : (t*n)*s ∈ NP := NP.mul_mem htn hsP
  have hdV : (t*n)*s ∈ NV := NV.mul_mem (NV.mul_mem htV hnV) hsV
  have hdH : (t*n)*s ∈ Elementary A hd hs hp ho K :=
    (Elementary A hd hs hp ho K).mul_mem ((Elementary A hd hs hp ho K).mul_mem
      (torusGroup_le_canonical A hs hp b₀ s₀ K ht)
      (wordUnit_mem_canonical A hd hs hp ho K w))
      (torusGroup_le_canonical A hs hp b₀ s₀ K hs')
  refine ⟨u*((t*n)*v*(t*n)⁻¹),(Positive A hd hs hp ho K).mul_mem hu hv',
    (t*n)*s,⟨⟨hdP,hdV⟩,hdH⟩,?_,?_⟩
  · have hdn := word_isDiag_of_linear_identity A hd hs hp ho K ε hε hA w hw
    change (wordUnit A hs hp b₀ s₀ K w : Matrix J₀ J₀ K).IsDiag at hdn
    obtain ⟨dt,hdt⟩ := torus_diagonal_of_mem A hs hp b₀ s₀ K t ht
    obtain ⟨ds,hds⟩ := torus_diagonal_of_mem A hs hp b₀ s₀ K s hs'
    change Matrix.IsDiag ((t : Matrix J₀ J₀ K)*(n : Matrix J₀ J₀ K)*(s : Matrix J₀ J₀ K))
    dsimp only [n]
    rw [hdt,hds,←hdn.diagonal_diag,Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]
    exact Matrix.isDiag_diagonal _
  · rw [he,hb,hc]
    dsimp only [n]
    group

theorem positive_mem_negative_normalizer_eq_one (hr : 2 ≤ r)
    (u : (Matrix J₀ J₀ K)ˣ) (hu : u ∈ Positive A hd hs hp ho K)
    (hn : u ∈ Subgroup.normalizer (Negative A hd hs hp ho K : Set (Matrix J₀ J₀ K)ˣ)) :
    u = 1 := by
  have hroot (i : Fin r) : u ∈ canonicalRootSubgroup D₀ K false i := by
    have hmem : u ∈ rootGroup A hs hp b₀ s₀ K false ⊓
        ((Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K true : Set _) ⊓
          canonicalElementaryGroup D₀ K) ⊔ canonicalRootSubgroup D₀ K false i) :=
      ⟨hu,(show Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K true : Set _) ⊓
        canonicalElementaryGroup D₀ K ≤ _ from le_sup_left)
          ⟨hn,positive_le_elementary A hd hs hp ho K hu⟩⟩
    have heq := opposite_normalizer_parabolic_intersection A hd hs hp ho K ε hε hA hidentity i
    rwa [heq] at hmem
  let i : Fin r := ⟨0,by omega⟩
  let j : Fin r := ⟨1,by omega⟩
  have hi := hroot i
  have hj := hroot j
  have hsimple (k : Fin r) :
      CFSGNormTwoCoordinateRootSubgroup.rootSubgroup A hd hs hp ho K (s₀ k) =
        canonicalRootSubgroup D₀ K false k :=
    rootSubgroup_simple_eq_canonical A hd hs hp ho K k
  rw [←hsimple i] at hi
  rw [←hsimple j] at hj
  exact eq_one_of_mem_two_roots A hd hs hp ho K (s₀ i) (s₀ j)
    (by
      intro h
      have hindex : s₀ i = s₀ j := Subtype.ext h
      have hij := (coordinateIndexEquiv A hd hs hp ho).injective hindex
      have hh := congrArg Fin.val hij
      norm_num [i,j] at hh) u hi hj

theorem diagonalNormalizer_isDiag (hr : 2 ≤ r)
    (g : (Matrix J₀ J₀ K)ˣ) (hg : g ∈ diagonalNormalizer A hd hs hp ho K) :
    (g : Matrix J₀ J₀ K).IsDiag := by
  obtain ⟨u,hu,d,hdD,hdiag,he⟩ := normalizer_envelope_factor A hd hs hp ho K ε hε hA hidentity g
    (diagonalNormalizer_le_envelope A hd hs hp ho K hg)
  have huV : u ∈ Subgroup.normalizer (Negative A hd hs hp ho K : Set (Matrix J₀ J₀ K)ˣ) := by
    have hh := (Subgroup.normalizer (Negative A hd hs hp ho K : Set (Matrix J₀ J₀ K)ˣ)).mul_mem
      hg.1.2 ((Subgroup.normalizer (Negative A hd hs hp ho K : Set (Matrix J₀ J₀ K)ˣ)).inv_mem hdD.1.2)
    rw [he,mul_inv_cancel_right] at hh
    exact hh
  have hu1 := positive_mem_negative_normalizer_eq_one A hd hs hp ho K ε hε hA hidentity hr u hu huV
  rw [hu1,one_mul] at he
  rw [he]
  exact hdiag

theorem diagonalNormalizer_commute (hr : 2 ≤ r)
    (g h : diagonalNormalizer A hd hs hp ho K) : Commute g h := by
  change g*h = h*g
  apply Subtype.ext
  apply Units.ext
  have hg := diagonalNormalizer_isDiag A hd hs hp ho K ε hε hA hidentity hr g.val g.property
  have hh := diagonalNormalizer_isDiag A hd hs hp ho K ε hε hA hidentity hr h.val h.property
  change (g.val : Matrix J₀ J₀ K)*(h.val : Matrix J₀ J₀ K) =
    (h.val : Matrix J₀ J₀ K)*(g.val : Matrix J₀ J₀ K)
  rw [←hg.diagonal_diag,←hh.diagonal_diag,Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]
  congr 1
  exact mul_comm _ _

local instance : LinearOrder (WeightBlock A) := blockOrder A

theorem envelope_block_triangular
    (g : (Matrix J₀ J₀ K)ˣ) (hg : g ∈ normalizerEnvelope A hd hs hp ho K) :
    (g : Matrix J₀ J₀ K).BlockTriangular (geckBlock A hd hs hp ho) := by
  obtain ⟨u,hu,d,_,hdiag,he⟩ := normalizer_envelope_factor A hd hs hp ho K ε hε hA hidentity g hg
  rw [he,Units.val_mul]
  apply (positive_block_triangular A hd hs hp ho K u hu).mul
  rw [←hdiag.diagonal_diag]
  exact Matrix.blockTriangular_diagonal _

theorem envelope_bruhat_block_unique (hr : 0 < r)
    (v w : List (Fin r)) (b₁ b₂ : (Matrix J₀ J₀ K)ˣ)
    (hb₁ : b₁ ∈ normalizerEnvelope A hd hs hp ho K)
    (hb₂ : b₂ ∈ normalizerEnvelope A hd hs hp ho K)
    (he : b₁*wordUnit A hs hp b₀ s₀ K v*b₂=wordUnit A hs hp b₀ s₀ K w) :
    wordBlockPermutation A hd hs hp ho v=wordBlockPermutation A hd hs hp ho w :=
  CFSGBlockMonomialBruhatUniqueness.block_bruhat_permutation_unique
    (geckBlock A hd hs hp ho) (geckBlock_surjective A hd hs hp ho hr) b₁ b₂ _ _
    (envelope_block_triangular A hd hs hp ho K ε hε hA hidentity b₁ hb₁)
    (envelope_block_triangular A hd hs hp ho K ε hε hA hidentity b₂ hb₂)
    (wordBlockPermutation A hd hs hp ho v) (wordBlockPermutation A hd hs hp ho w)
    (word_block_support A hd hs hp ho K v) (word_block_support A hd hs hp ho K w) he

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNormalizerEnvelope
