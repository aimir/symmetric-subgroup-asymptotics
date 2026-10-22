import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCartanKernel
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWordLatticeSupport
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckDiagonalKernel
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNormalizerWord
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckBorelPowerElements
import SymmetricSubgroupAsymptotics.CFSGDiagonalUnipotentExtension

/-! Actual positive-normalizer elements factor into the original positive
group and an arbitrary diagonal unit once their actual normalizing Weyl
words act trivially on the root lattice. This is weaker than normalizer=B,
and suffices for the Sylow maximality criterion. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNormalizerDiagonalFactor
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGGradedMatrixSupport
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoGeckLatticeDegree
open CFSGNormTwoGeckWordLatticeSupport CFSGNormTwoCoordinateCartanKernel
open CFSGNormTwoGeckDiagonalKernel CFSGNormTwoCoordinateNormalizerWord
open CFSGNormTwoGeckBorelEnvelope CFSGNormTwoGeckBorelFactorization
open CFSGNormTwoGeckBorelNormalization CFSGNormTwoGeckBorelPowerElements
open CFSGNormTwoCoordinateHeight CFSGNormTwoGeckHeightSupport
open CFSGSerreQuadraticMatrix CFSGNormTwoGeckIntegralRealization
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀j,A j j=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem word_isDiag_of_linear_identity (K : Type) [Field K]
    (ε : Fin r→ℤ) (hε : ∀i,ε i*ε i=1)
    (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (w : List (Fin r)) (hw : wordLinear A hs hp b₀ s₀ w=1) :
    (wordUnit A hs hp b₀ s₀ K w : Matrix
      ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K).IsDiag := by
  apply isDiag_of_preserves_of_fixes_zero (latticeWeight A hs hp b₀)
    (lattice_nonzero_fibres A hs hp b₀) _
    (word_preserves_lattice_of_linear_identity A hs hp b₀ s₀ K w hw)
  intro j hj
  cases j with
  | inl j=>exact word_fixes_cartan_of_lattice_identity A hd hs hp ho K ε hε hA w hw j
  | inr j=>
    change j.val=0 at hj
    have hn := j.property
    rw [hj] at hn
    norm_num [integerPairing] at hn

theorem normalizer_diagonal_factor (K : Type) [Field K]
    (ε : Fin r→ℤ) (hε : ∀i,ε i*ε i=1)
    (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (hidentity : ∀w : List (Fin r),wordUnit A hs hp b₀ s₀ K w∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)→
      wordLinear A hs hp b₀ s₀ w=1)
    (g : (Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)ˣ)
    (hg : g∈canonicalElementaryGroup (realizationData A hs hp b₀ s₀) K)
    (hN : g∈Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)) :
    ∃u∈rootGroup A hs hp b₀ s₀ K false,∃d :
      (Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)ˣ,
      (d : Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K).IsDiag ∧ g=u*d := by
  obtain ⟨w,b,hb,c,hc,he,hn,_⟩ := normalizer_word_reduction A hd hs hp ho K g hg hN
  obtain ⟨u,hu,t,ht,hb⟩ := borel_factor A hs hp b₀ s₀ K b hb
  obtain ⟨v,hv,s,hs',hc⟩ := borel_factor A hs hp b₀ s₀ K c hc
  have hdn := word_isDiag_of_linear_identity A hd hs hp ho K ε hε hA w (hidentity w hn)
  obtain ⟨dt,hdt⟩ := torus_diagonal_of_mem A hs hp b₀ s₀ K t ht
  obtain ⟨ds,hds⟩ := torus_diagonal_of_mem A hs hp b₀ s₀ K s hs'
  let n := wordUnit A hs hp b₀ s₀ K w
  let N : Subgroup ((Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)ˣ) :=
    Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)
  have htN : t∈N := borelEnvelope_le_normalizer_positive A hs hp b₀ s₀ K
    ((show torusGroup A hs hp b₀ s₀ K≤borelEnvelope A hs hp b₀ s₀ K from le_sup_right) ht)
  have htn : t*n∈N := N.mul_mem htN hn
  have hv' : (t*n)*v*(t*n)⁻¹∈rootGroup A hs hp b₀ s₀ K false :=
    (Subgroup.mem_normalizer_iff.mp htn v).mp hv
  refine ⟨u*((t*n)*v*(t*n)⁻¹),(rootGroup A hs hp b₀ s₀ K false).mul_mem hu hv',
    (t*n)*s,?_,?_⟩
  · change Matrix.IsDiag
      ((t : Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)*
       (n : Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)*
       (s : Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K))
    dsimp only [n]
    rw [hdt,hds,←hdn.diagonal_diag,Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]
    exact Matrix.isDiag_diagonal _
  · rw [he,hb,hc]
    dsimp only [n]
    group

theorem pSubgroup_normalizer_le_positive (K : Type) [Field K]
    (ε : Fin r→ℤ) (hε : ∀i,ε i*ε i=1)
    (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (hidentity : ∀w : List (Fin r),wordUnit A hs hp b₀ s₀ K w∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)→
      wordLinear A hs hp b₀ s₀ w=1)
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (P : Subgroup ((Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)ˣ))
    (hP : IsPGroup p P) (hPH : P≤canonicalElementaryGroup (realizationData A hs hp b₀ s₀) K)
    (hPN : P≤Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)) :
    P≤rootGroup A hs hp b₀ s₀ K false := by
  obtain ⟨e,he⟩ := CFSGFiniteWeightFlag.exists_flag (weight A hs hp b₀ coordinateHeight)
  apply CFSGDiagonalUnipotentExtension.pSubgroup_le e
    (Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _) ⊓
      canonicalElementaryGroup (realizationData A hs hp b₀ s₀) K)
    (rootGroup A hs hp b₀ s₀ K false) P
    (positive_le_unipotent A hs hp b₀ s₀ coordinateHeight (simple_height A hd hs hp ho) K e he)
    (fun g hg=>normalizer_diagonal_factor A hd hs hp ho K ε hε hA hidentity g hg.2 hg.1)
    p hP
  exact le_inf hPN hPH

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNormalizerDiagonalFactor
