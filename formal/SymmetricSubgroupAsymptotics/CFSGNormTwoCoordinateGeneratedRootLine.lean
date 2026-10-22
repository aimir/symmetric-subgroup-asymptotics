import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateGeneratedSimpleLine
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckGeneratedLieInvariance
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRootWordOrbit
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWordLatticeSupport
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCartan

/-! Arbitrary-root line recognition INSIDE the original generated rational
Geck Lie algebra. A literal integral reflection word reduces the degree
to a negative simple degree; conjugation preserves the same Lie algebra.
The spanning matrix is the corresponding actual Weyl conjugate of F_i. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateGeneratedRootLine
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckLatticeDegree CFSGGradedMatrixSupport
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylWordAlgebra
open CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoGeckWordLatticeSupport
variable {r : ℕ}
    (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
private abbrev CoordMat := Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) ℚ
local notation "Mat" => CoordMat A hd hs hp ho
local notation "ell" => latticeWeight A hs hp b₀
local notation "act" => CFSGAlgebraConjugationAction.action ℚ Mat

theorem word_degree_line (w : List (Fin r)) (j : Fin r)
    (M : Mat) (hM : M∈RootPairing.GeckConstruction.lieAlgebra b₀)
    (hdeg : Supported ell
      (fun v=>v+wordLinear A hs hp b₀ s₀ w (-(s₀ j:Roots A).val)) M) :
    ∃c : ℚ,M=c • act (wordUnit A hs hp b₀ s₀ ℚ w)
      (RootPairing.GeckConstruction.f (s₀ j)) := by
  let u := wordUnit A hs hp b₀ s₀ ℚ w
  let e := wordLinear A hs hp b₀ s₀ w
  let N : Mat := act u⁻¹ M
  have hN : N∈RootPairing.GeckConstruction.lieAlgebra b₀ := by
    have hh := CFSGNormTwoGeckGeneratedLieInvariance.word_action_mem_generated
      A hs hp b₀ s₀ (inverseWord w) M hM
    rw [wordUnit_inverseWord] at hh
    exact hh
  have hP := word_lattice_support A hs hp b₀ s₀ ℚ (inverseWord w)
  rw [wordUnit_inverseWord,wordLinear_inverseWord] at hP
  have hQ := word_lattice_support A hs hp b₀ s₀ ℚ w
  have hNdeg : Supported ell (fun v=>v-(s₀ j:Roots A).val) N := by
    have hh := supported_conjugation ell e.symm.toAddEquiv
      (e (-(s₀ j:Roots A).val)) _ M _ hP hdeg hQ
    have he : e.symm (e (-(s₀ j:Roots A).val))= -(s₀ j:Roots A).val :=
      e.symm_apply_apply _
    change Supported ell (fun x=>x+e.symm (e (-(s₀ j:Roots A).val)))
      (((u⁻¹ : (Mat)ˣ) : Mat)*M*(u : Mat)) at hh
    rw [he] at hh
    simpa only [N,CFSGAlgebraConjugationAction.action_apply,inv_inv,sub_eq_add_neg] using hh
  obtain ⟨c,hc⟩ := CFSGNormTwoCoordinateGeneratedSimpleLine.negative_simple_line
    A hd hs hp ho (s₀ j) N hN hNdeg
  refine ⟨c,?_⟩
  have hh := congrArg (act u) hc
  have hcancel : act u N=M := by
    change (act u*act u⁻¹) M=M
    rw [←map_mul,mul_inv_cancel,map_one]
    rfl
  rw [hcancel,map_smul] at hh
  exact hh

theorem arbitrary_root_line (k : Roots A) :
    ∃ (w : List (Fin r)) (j : Fin r),
      k.val=wordLinear A hs hp b₀ s₀ w (-(s₀ j:Roots A).val) ∧
      ∀ (M : Mat),M∈RootPairing.GeckConstruction.lieAlgebra b₀→
        Supported ell (fun v=>v+k.val) M→
        ∃c : ℚ,M=c • act (wordUnit A hs hp b₀ s₀ ℚ w)
          (RootPairing.GeckConstruction.f (s₀ j)) := by
  obtain ⟨w,j,hk⟩ := CFSGNormTwoGeckRootWordOrbit.exists_word_linear_negative A hs hp b₀ s₀ k
  refine ⟨w,j,hk,?_⟩
  intro M hM hdeg
  rw [hk] at hdeg
  exact word_degree_line A hd hs hp ho w j M hM hdeg

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateGeneratedRootLine
