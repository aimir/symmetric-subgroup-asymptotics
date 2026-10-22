import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateEdgeBracketCoordinates
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOrthogonalBracketZero
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOffDiagonalCollecting
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateDerivedSecondLayer

/-! The actual second layer has UNIQUE adjacent-edge coefficients in
every field. Diagonal brackets vanish, orthogonal brackets descend from
the original rational Serre relation, and reversed edges change sign.
The coefficient family is derived internally for the SAME actual U. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSecondEdgeCoordinates
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGGeckSerreRepresentation
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckHeightSupport CFSGNormTwoCoordinateHeight CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoCoordinateEdgeBracketCoordinates CFSGNormTwoGeckOrthogonalBracketZero
open CFSGNormTwoGeckOffDiagonalCollecting CFSGGradedMatrixDerivedSecondLayer
open CFSGGradedMatrixGroupSecondLayer CFSGNormTwoCoordinateDerivedSecondLayer
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀
local notation "w" => weight A hs hp b₀ coordinateHeight
local notation "U" => rootGroup A hs hp b₀ s₀ K false

theorem simple_bracket_mem_edge_span (i j : Fin r) :
    ⁅fieldRoot D K false i,fieldRoot D K false j⁆∈
      Submodule.span K (Set.range (edgeBracket A hd hs hp ho K)) := by
  classical
  by_cases hij : i=j
  · subst j
    rw [lie_self]
    exact Submodule.zero_mem _
  rcases cartan_zero_or_neg_one A hs hp b₀ s₀ i j hij with hz|hn
  · rw [orthogonal_bracket_zero A hs hp b₀ s₀ K i j hz]
    exact Submodule.zero_mem _
  · have hA : A i j= -1 := by
      change (b₀).cartanMatrix (s₀ j) (s₀ i)= -1 at hn
      rwa [coordinate_cartan_transpose A hd hs hp ho] at hn
    by_cases hlt : i<j
    · exact Submodule.subset_span ⟨(⟨(i,j),hlt,hA⟩ : Edge A),rfl⟩
    · have hgt : j < i := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hij)
      have hrev : A j i= -1 := by
        rw [←hA]
        exact congrFun (congrFun hs i) j
      have hm : edgeBracket A hd hs hp ho K (⟨(j,i),hgt,hrev⟩ : Edge A)∈
          Submodule.span K (Set.range (edgeBracket A hd hs hp ho K)) :=
        Submodule.subset_span ⟨(⟨(j,i),hgt,hrev⟩ : Edge A),rfl⟩
      simpa only [edgeBracket,lie_skew] using (Submodule.neg_mem _ hm)

theorem bracketSpan_le_edge_span :
    bracketSpan (fun i : Fin r=>fieldRoot D K false i)≤
      Submodule.span K (Set.range (edgeBracket A hd hs hp ho K)) := by
  apply Submodule.span_le.mpr
  rintro M ⟨p,rfl⟩
  exact simple_bracket_mem_edge_span A hd hs hp ho K p.1 p.2

theorem derived_secondLayer_unique_edge_coefficients (u : U) (hu : u∈commutator U) :
    ∃!c : Edge A→K,(∑p,c p • edgeBracket A hd hs hp ho K p)=secondLayer w u.val := by
  classical
  have hspan := bracketSpan_le_edge_span A hd hs hp ho K
    (derived_secondLayer_mem A hd hs hp ho K u hu)
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hspan
  refine ⟨c,hc,?_⟩
  intro d hd'
  exact edge_coefficients_unique A hd hs hp ho K d c (hd'.trans hc.symm)

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSecondEdgeCoordinates
