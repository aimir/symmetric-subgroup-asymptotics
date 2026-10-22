import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootIntersection

/-! Faithful ORIGINAL root labels for actual canonical matrix subgroups.
This is not a claim about arbitrary automorphisms or about a projective
central quotient. Nontriviality and distinctness hold in every field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootLabels
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckLatticeDegree
open CFSGNormTwoGeckIntegralWord CFSGNormTwoGeckNegativeWordCoefficients
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWordRootTransport
open CFSGNormTwoCoordinateRootSubgroup CFSGNormTwoRootDegreeSeparation
open CFSGGradedMatrixSingleDegreeSpan CFSGGradedQuadraticFirstCoefficient
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀
local notation "ell" => latticeWeight A hs hp b₀

theorem selected_root_one_ne_one (K : Type) [Field K] (k : Roots A) :
    rootWord D K (rootWitness A hd hs hp ho k).val.1 true
      (rootWitness A hd hs hp ho k).val.2 1≠1 := by
  let p := rootWitness A hd hs hp ho k
  intro hz
  have hE := first_support A hs hp b₀ s₀ K p.val.1 p.val.2
  have hD := second_support A hs hp b₀ s₀ K p.val.1 p.val.2
  rw [←p.property] at hE hD
  have he : ((rootWord D K p.val.1 true p.val.2 1) :
      Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)=
        1+firstCoefficient A hs hp b₀ s₀ K p.val.1 p.val.2+
          secondCoefficient A hs hp b₀ s₀ K p.val.1 p.val.2 := by
    simpa only [rootWord,word_eq_canonicalWord,one_smul,one_pow] using
      word_expansion A hs hp b₀ s₀ K p.val.1 p.val.2 1
  rw [hz,Units.val_one] at he
  have hh := congrArg (degreePart ell k.val) he.symm
  rw [degreePart_quadratic ell k.val _ _ hE hD
    (root_val_ne_zero A k) (root_val_ne_double A k k),
    degreePart_one_zero ell k.val (root_val_ne_zero A k)] at hh
  exact (first_ne_zero A hs hp b₀ s₀ K p.val.1 p.val.2) hh

theorem rootSubgroup_ne_bot (K : Type) [Field K] (k : Roots A) :
    rootSubgroup A hd hs hp ho K k≠⊥ := by
  intro hk
  let p := rootWitness A hd hs hp ho k
  have hu : rootWord D K p.val.1 true p.val.2 1∈rootSubgroup A hd hs hp ho K k :=
    (mem_wordRootSubgroup_iff A hd hs hp ho K p.val.1 p.val.2 _).mpr ⟨1,rfl⟩
  rw [hk] at hu
  exact selected_root_one_ne_one A hd hs hp ho K k (Subgroup.mem_bot.mp hu)

theorem rootSubgroup_injective (K : Type) [Field K] :
    Function.Injective (rootSubgroup A hd hs hp ho K) := by
  intro k l he
  by_contra hkl
  have hcap := CFSGNormTwoCoordinateRootIntersection.rootSubgroup_inf_eq_bot A hd hs hp ho K k l hkl
  rw [←he,inf_idem] at hcap
  exact rootSubgroup_ne_bot A hd hs hp ho K k hcap

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootLabels
