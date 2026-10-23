import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNormalizerEnvelope
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateBorelRootNormalization

/-! Every element in the actual simultaneous positive/opposite normalizer
normalizes EVERY literal root line. The proof retains torus/identity-word
factors from Bruhat reduction and kills the remaining positive factor;
it does not recognize the entire lattice kernel as a torus. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootNormalizerEnvelope
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoCoordinateNormalizerEnvelope CFSGNormTwoCoordinateRootLineNormalizers
open CFSGNormTwoCoordinateNormalizerWord CFSGNormTwoGeckBorelFactorization
open CFSGNormTwoGeckBorelEnvelope CFSGNormTwoGeckIntegralWord
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoCoordinateRootSubgroup
open CFSGNormTwoCoordinateBorelRootNormalization
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀j,A j j=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "J₀" => CFSGNormTwoCoordinateWeylBlocks.GeckIndex A hd hs hp ho

theorem diagonalNormalizer_le_normalizer_root (K : Type) [Field K]
    (ε : Fin r→ℤ) (hε : ∀i,ε i*ε i=1)
    (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (hidentity : ∀w : List (Fin r),wordUnit A hs hp b₀ s₀ K w∈
      Subgroup.normalizer (Positive A hd hs hp ho K : Set _)→wordLinear A hs hp b₀ s₀ w=1)
    (hr : 2 ≤ r) (k : Roots A) :
    diagonalNormalizer A hd hs hp ho K ≤ Subgroup.normalizer (rootSubgroup A hd hs hp ho K k : Set _) := by
  intro g hg
  obtain ⟨w,b,hb,c,hc,he,hn,_⟩ := normalizer_word_reduction A hd hs hp ho K g hg.2 hg.1.1
  obtain ⟨u,hu,t,ht,hb⟩ := borel_factor A hs hp b₀ s₀ K b hb
  obtain ⟨v,hv,s,hs',hc⟩ := borel_factor A hs hp b₀ s₀ K c hc
  let n := wordUnit A hs hp b₀ s₀ K w
  let NP := Subgroup.normalizer (Positive A hd hs hp ho K : Set (Matrix J₀ J₀ K)ˣ)
  let NV := Subgroup.normalizer (Negative A hd hs hp ho K : Set (Matrix J₀ J₀ K)ˣ)
  let NR := Subgroup.normalizer (rootSubgroup A hd hs hp ho K k : Set (Matrix J₀ J₀ K)ˣ)
  have hw := hidentity w hn
  have hnV : n∈NV := by
    dsimp only [n,NV,Negative]
    rw [word_eq_canonicalWord]
    exact identity_word_normalizes A hd hs hp ho K w hw true
  have htP : t∈NP := torusGroup_normalizes A hd hs hp ho K false ht
  have htV : t∈NV := torusGroup_normalizes A hd hs hp ho K true ht
  have hsV : s∈NV := torusGroup_normalizes A hd hs hp ho K true hs'
  have htn : t*n∈NP := NP.mul_mem htP hn
  have hvU : (t*n)*v*(t*n)⁻¹∈Positive A hd hs hp ho K :=
    (Subgroup.mem_normalizer_iff.mp htn v).mp hv
  let up := u*((t*n)*v*(t*n)⁻¹)
  let dp := (t*n)*s
  have hup : up∈Positive A hd hs hp ho K := (Positive A hd hs hp ho K).mul_mem hu hvU
  have hdpV : dp∈NV := NV.mul_mem (NV.mul_mem htV hnV) hsV
  have heq : g=up*dp := by
    rw [he,hb,hc]
    dsimp only [up,dp,n]
    group
  have hupV : up∈NV := by
    have hh := NV.mul_mem hg.1.2 (NV.inv_mem hdpV)
    rw [heq,mul_inv_cancel_right] at hh
    exact hh
  have hup1 := positive_mem_negative_normalizer_eq_one A hd hs hp ho K ε hε hA hidentity hr up hup hupV
  have hgdp : g=dp := by simpa only [hup1,one_mul] using heq
  have hnR : n∈NR := by
    apply Subgroup.mem_normalizer_iff_conj_image_eq.mpr
    have hh := identity_word_root_line A hd hs hp ho K w hw k
    dsimp only [n,NR]
    rw [word_eq_canonicalWord]
    exact congrArg (fun S : Subgroup (Matrix J₀ J₀ K)ˣ=>(S : Set (Matrix J₀ J₀ K)ˣ)) hh
  have htR : t∈NR := torusGroup_le_normalizer_root A hd hs hp ho K k ht
  have hsR : s∈NR := torusGroup_le_normalizer_root A hd hs hp ho K k hs'
  rw [hgdp]
  exact NR.mul_mem (NR.mul_mem htR hnR) hsR

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootNormalizerEnvelope
