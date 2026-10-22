import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateReflectionWords
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateGeneratedMixedDegree
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckGeneratedLieInvariance
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWordLatticeSupport
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylWordAlgebra

/-! Actual generated rational Geck Lie elements of nonnegative norm-four
or norm-six degree vanish. An explicit integer reflection descent reaches
mixed signs; the SAME actual Weyl-word conjugation transports membership
and degree. No ambient-matrix homogeneity or Lie recognition shortcut. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNonrootDegreeZero
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckLatticeDegree CFSGGradedMatrixSupport
open CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoGeckWordLatticeSupport
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylWordAlgebra
open CFSGNormTwoCoordinateReflectionWords CFSGNormTwoGeckGeneratedLieInvariance
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
private abbrev CoordMat := Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) ℚ
local notation "Mat" => CoordMat A hd hs hp ho
local notation "ell" => latticeWeight A hs hp b₀

theorem nonnegative_norm_four_or_six_degree_zero (M : Mat) (d : Fin r→ℤ)
    (hM : M∈RootPairing.GeckConstruction.lieAlgebra b₀)
    (hdeg : Supported ell (fun v=>v+d) M) (hdnonneg : ∀i,0≤d i)
    (hnorm : integerPairing A d d=4 ∨ integerPairing A d d=6) : M=0 := by
  obtain ⟨w,a,b,ha,hb⟩ := exists_mixed_wordLinear A hd hs hp ho d hdnonneg hnorm
  let P : Matˣ := wordUnit A hs hp b₀ s₀ ℚ w
  let N : Mat := CFSGAlgebraConjugationAction.action ℚ Mat P M
  have hN : N∈RootPairing.GeckConstruction.lieAlgebra b₀ :=
    word_action_mem_generated A hs hp b₀ s₀ w M hM
  have hP := word_lattice_support A hs hp b₀ s₀ ℚ w
  have hQ := word_lattice_support A hs hp b₀ s₀ ℚ (inverseWord w)
  rw [wordUnit_inverseWord,wordLinear_inverseWord] at hQ
  have hNdeg : Supported ell (fun v=>v+wordLinear A hs hp b₀ s₀ w d) N :=
    supported_conjugation ell (wordLinear A hs hp b₀ s₀ w).toAddEquiv d _ _ _ hP hdeg hQ
  have hz : N=0 := CFSGNormTwoCoordinateGeneratedMixedDegree.mixed_degree_zero
    A hd hs hp ho N _ hN hNdeg a b ha hb
  apply (CFSGAlgebraConjugationAction.action ℚ Mat P).injective
  simpa only [map_zero] using hz

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNonrootDegreeZero
