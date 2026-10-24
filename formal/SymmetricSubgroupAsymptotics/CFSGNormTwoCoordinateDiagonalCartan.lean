import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootNormalizerEnvelope
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCartanKernel

/-! The actual simultaneous positive/opposite normalizer fixes every
Cartan column. Retaining the torus/identity-word factors in Bruhat
reduction proves this without identifying that normalizer with a torus.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateDiagonalCartan
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoCoordinateNormalizerEnvelope CFSGNormTwoCoordinateNormalizerWord
open CFSGNormTwoGeckBorelFactorization CFSGNormTwoGeckBorelEnvelope
open CFSGNormTwoGeckParameterizedTorus CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoGeckIntegralRealization
open CFSGNormTwoCoordinateCartanKernel CFSGNormTwoGeckIntegralWord
open CFSGNormTwoCoordinateRootLineNormalizers
variable {r:ℕ} (A:Matrix (Fin r) (Fin r) ℤ) (hd:∀i,A i i=2)
    (hs:A.transpose=A) (hp:(rationalMatrix A).PosDef) (ho:∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "J₀" => CFSGNormTwoCoordinateWeylBlocks.GeckIndex A hd hs hp ho

def cartanFixer (K:Type) [Field K] : Subgroup (Matrix J₀ J₀ K)ˣ where
  carrier:={g|∀j:(b₀).support,(g:Matrix J₀ J₀ K)*ᵥPi.single (.inl j) 1=Pi.single (.inl j) 1}
  one_mem':=by intro j;exact Matrix.one_mulVec _
  mul_mem':=by
    intro g h hg hh j
    change ((g:Matrix J₀ J₀ K)*(h:Matrix J₀ J₀ K))*ᵥ_= _
    rw [←Matrix.mulVec_mulVec,hh j,hg j]
  inv_mem':=by
    intro g hg j
    have he:=congrArg (fun v:J₀→K=>(↑(g⁻¹):Matrix J₀ J₀ K)*ᵥv) (hg j)
    dsimp only at he
    rw [Matrix.mulVec_mulVec,←Units.val_mul,inv_mul_cancel,Units.val_one,Matrix.one_mulVec] at he
    exact he.symm

theorem torusGroup_le_cartanFixer (K:Type) [Field K] :
    torusGroup A hs hp b₀ s₀ K≤cartanFixer A hd hs hp ho K := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨⟨i,t⟩,rfl⟩ j
  exact torus_cartan A hs hp b₀ s₀ K i t j

theorem diagonalNormalizer_le_cartanFixer (K:Type) [Field K]
    (ε:Fin r→ℤ) (hε:∀i,ε i*ε i=1)
    (hA:∀i j,ε i*|A i j|=A j i*ε j)
    (hidentity:∀w:List (Fin r),wordUnit A hs hp b₀ s₀ K w∈
      Subgroup.normalizer (Positive A hd hs hp ho K:Set _)→wordLinear A hs hp b₀ s₀ w=1)
    (hr:2≤r) : diagonalNormalizer A hd hs hp ho K≤cartanFixer A hd hs hp ho K := by
  intro g hg
  obtain ⟨w,b,hb,c,hc,he,hn,_⟩:=normalizer_word_reduction A hd hs hp ho K g hg.2 hg.1.1
  obtain ⟨u,hu,t,ht,hb⟩:=borel_factor A hs hp b₀ s₀ K b hb
  obtain ⟨v,hv,s,hs',hc⟩:=borel_factor A hs hp b₀ s₀ K c hc
  let n:=wordUnit A hs hp b₀ s₀ K w
  let NP:=Subgroup.normalizer (Positive A hd hs hp ho K:Set (Matrix J₀ J₀ K)ˣ)
  let NV:=Subgroup.normalizer (Negative A hd hs hp ho K:Set (Matrix J₀ J₀ K)ˣ)
  have hw:=hidentity w hn
  have hnV:n∈NV := by
    dsimp only [n,NV,Negative]
    rw [word_eq_canonicalWord]
    exact identity_word_normalizes A hd hs hp ho K w hw true
  have htP:t∈NP:=torusGroup_normalizes A hd hs hp ho K false ht
  have htV:t∈NV:=torusGroup_normalizes A hd hs hp ho K true ht
  have hsV:s∈NV:=torusGroup_normalizes A hd hs hp ho K true hs'
  have htn:t*n∈NP:=NP.mul_mem htP hn
  have hvU:(t*n)*v*(t*n)⁻¹∈Positive A hd hs hp ho K:=
    (Subgroup.mem_normalizer_iff.mp htn v).mp hv
  let up:=u*((t*n)*v*(t*n)⁻¹)
  let dp:=(t*n)*s
  have hup:up∈Positive A hd hs hp ho K:=(Positive A hd hs hp ho K).mul_mem hu hvU
  have hdpV:dp∈NV:=NV.mul_mem (NV.mul_mem htV hnV) hsV
  have heq:g=up*dp := by
    rw [he,hb,hc]
    dsimp only [up,dp,n]
    group
  have hupV:up∈NV := by
    have hh:=NV.mul_mem hg.1.2 (NV.inv_mem hdpV)
    rw [heq,mul_inv_cancel_right] at hh
    exact hh
  have hup1:=positive_mem_negative_normalizer_eq_one A hd hs hp ho K ε hε hA hidentity hr up hup hupV
  have hgdp:g=dp := by simpa only [hup1,one_mul] using heq
  have hnC:n∈cartanFixer A hd hs hp ho K:=
    word_fixes_cartan_of_lattice_identity A hd hs hp ho K ε hε hA w hw
  rw [hgdp]
  exact (cartanFixer A hd hs hp ho K).mul_mem
    ((cartanFixer A hd hs hp ho K).mul_mem (torusGroup_le_cartanFixer A hd hs hp ho K ht) hnC)
    (torusGroup_le_cartanFixer A hd hs hp ho K hs')

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateDiagonalCartan
