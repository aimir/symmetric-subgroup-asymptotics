import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWeylIntersectionCardinality

/-! Root-sign containment gives containment of the full positive Weyl
intersections. These are the actual sign parts, rather than recursively
peeled residual subgroups. No converse to a residual containment is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWeylPositivePartMonotonicity
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoCoordinatePositiveRootGenerators
open CFSGNormTwoCoordinateWeylIntersectionFactor
open CFSGNormTwoCoordinateWeylIntersectionCardinality
open CFSGNormTwoGeckWeylWordDegree
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ i, A i i = 2)
    (hs : A.transpose = A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀ i j, i ≠ j → A i j ≤ 0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem sign_part_le_of_roots_subset (K : Type) [Field K] [Finite K]
    (w v : List (Fin r)) (neg : Bool)
    (hroots : signRoots A hd hs hp ho w neg ⊆ signRoots A hd hs hp ho v neg) :
    wordSignPart A hd hs hp ho K w neg ≤ wordSignPart A hd hs hp ho K v neg := by
  rw [← signRootGroup_eq_part A hd hs hp ho K w neg]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨k, a, rfl⟩
  exact parameter_mem_part A hd hs hp ho K v neg ⟨k.val, hroots k.property⟩ a

theorem positive_part_le_of_root_implication (K : Type) [Field K] [Finite K]
    (w v : List (Fin r))
    (hroot : ∀ k : PositiveRoot A,
      (∀ j, 0 ≤ (wordRoot A hs hp b₀ s₀ w k.val).val j) →
      ∀ j, 0 ≤ (wordRoot A hs hp b₀ s₀ v k.val).val j) :
    wordSignPart A hd hs hp ho K w false ≤ wordSignPart A hd hs hp ho K v false := by
  apply sign_part_le_of_roots_subset A hd hs hp ho K w v false
  intro k hk
  have hw : ∀ j, 0 ≤ (wordRoot A hs hp b₀ s₀ w k.val).val j := by
    simpa only [signRoots, Bool.false_eq_true, if_false, Finset.mem_filter,
      Finset.mem_univ, true_and] using hk
  simpa only [signRoots, Bool.false_eq_true, if_false, Finset.mem_filter,
    Finset.mem_univ, true_and] using hroot k hw

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWeylPositivePartMonotonicity
