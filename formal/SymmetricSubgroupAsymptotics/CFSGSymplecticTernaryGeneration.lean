import SymmetricSubgroupAsymptotics.CFSGSymplecticTernaryExtraction
import SymmetricSubgroupAsymptotics.CFSGSymplecticInitialRootCoverage
import SymmetricSubgroupAsymptotics.MarkedC4GeneratorNumbers

/-! The literal ternary generating pair in every symplectic rank at
least two: the second upper long root and the cleaned mixed Coxeter word. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticTernaryGeneration
open CFSGSymplecticSerreMatrices CFSGSymplecticTernaryExtraction

def ternaryFirst (K : Type) [Field K] (s : ℕ) : elementaryRootGroup K (s + 2) :=
  secondLongRoot K (s + 1) 1

def ternarySecond (K : Type) [Field K] (s : ℕ) : elementaryRootGroup K (s + 2) :=
  cleanMixedWeyl K (s + 1)

theorem ternary_pair_generate {K : Type} [Field K] [Finite K]
    (hcard : Nat.card K = 3) (s : ℕ) :
    Subgroup.closure ({ternaryFirst K s, ternarySecond K s} :
      Set (elementaryRootGroup K (s + 2))) = ⊤ := by
  let H := Subgroup.closure ({ternaryFirst K s, ternarySecond K s} :
    Set (elementaryRootGroup K (s + 2)))
  have hx : secondLongRoot K (s + 1) 1 ∈ H :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hy : cleanMixedWeyl K (s + 1) ∈ H :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  obtain ⟨hW, hA, hB⟩ := pair_extract hcard (s + 1) (by omega) H hx hy
  exact elementary_eq_top_of_initial_root_lines K (s + 1) (by omega) H hW hA hB

theorem elementary_exists_generating_pair {K : Type} [Field K] [Finite K]
    (hcard : Nat.card K = 3) (s : ℕ) :
    ∃ x y : elementaryRootGroup K (s + 2),
      Subgroup.closure ({x, y} : Set (elementaryRootGroup K (s + 2))) = ⊤ :=
  ⟨ternaryFirst K s, ternarySecond K s, ternary_pair_generate hcard s⟩

theorem elementary_genRank_le_two {K : Type} [Field K] [Finite K]
    (hcard : Nat.card K = 3) (s : ℕ) :
    MarkedC4.genRank (elementaryRootGroup K (s + 2)) ≤ 2 := by
  have hc : Subgroup.closure
      (({ternaryFirst K s, ternarySecond K s} :
        Finset (elementaryRootGroup K (s + 2))) :
        Set (elementaryRootGroup K (s + 2))) = ⊤ := by
    simpa only [Finset.coe_insert, Finset.coe_singleton] using ternary_pair_generate hcard s
  exact (MarkedC4.genRank_le hc).trans Finset.card_le_two

end SymmetricSubgroupAsymptotics.CFSGSymplecticTernaryGeneration
