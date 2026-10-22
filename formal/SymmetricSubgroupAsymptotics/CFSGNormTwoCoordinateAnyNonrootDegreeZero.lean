import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNonrootDegreeZero

/-! Arbitrary-sign norm-four and norm-six degrees vanish in the SAME
generated rational Geck Lie algebra. A negative vector is handled by
linearity of an actual reflection word on its positive negative, not by
an assumed opposition action or a root-space classification theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateAnyNonrootDegreeZero
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

theorem exists_mixed_word_norm_four_or_six (d : Fin r→ℤ)
    (hnorm : integerPairing A d d=4 ∨ integerPairing A d d=6) :
    ∃w : List (Fin r),∃a b : Fin r,
      0<wordLinear A hs hp b₀ s₀ w d a ∧ wordLinear A hs hp b₀ s₀ w d b<0 := by
  classical
  by_cases hnonneg : ∀j,0≤d j
  · exact exists_mixed_wordLinear A hd hs hp ho d hnonneg hnorm
  obtain ⟨b,hb⟩ : ∃b,d b<0 := by
    simpa only [not_forall,not_le] using hnonneg
  by_cases hpos : ∃a,0<d a
  · obtain ⟨a,ha⟩ := hpos
    refine ⟨[],a,b,?_,?_⟩
    · change 0<d a
      exact ha
    · change d b<0
      exact hb
  have hnegative : ∀j,0≤(-d) j := by
    intro j
    have hj : ¬0<d j := fun hj=>hpos ⟨j,hj⟩
    change 0≤ -(d j)
    omega
  have hnormneg : integerPairing A (-d) (-d)=4 ∨ integerPairing A (-d) (-d)=6 := by
    simpa only [map_neg,LinearMap.neg_apply,neg_neg] using hnorm
  obtain ⟨w,a,c,ha,hc⟩ := exists_mixed_wordLinear A hd hs hp ho (-d) hnegative hnormneg
  rw [map_neg] at ha hc
  change 0< -(wordLinear A hs hp b₀ s₀ w d a) at ha
  change -(wordLinear A hs hp b₀ s₀ w d c)<0 at hc
  exact ⟨w,c,a,by omega,by omega⟩

theorem norm_four_or_six_degree_zero (M : Mat) (d : Fin r→ℤ)
    (hM : M∈RootPairing.GeckConstruction.lieAlgebra b₀)
    (hdeg : Supported ell (fun v=>v+d) M)
    (hnorm : integerPairing A d d=4 ∨ integerPairing A d d=6) : M=0 := by
  obtain ⟨w,a,b,ha,hb⟩ := exists_mixed_word_norm_four_or_six A hd hs hp ho d hnorm
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

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateAnyNonrootDegreeZero
