import SymmetricSubgroupAsymptotics.BoundedNilpotentCoreGeneration

/-! The bounded-orbit consumer of nilpotent-core generation follows from
actual orbit images and the proved mixed-prime abelian-section estimate. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.OrdinaryNilpotentGeneration

def nilpotentControlCutoff (C : ℕ) : ℕ := C.factorial*((C.factorial).factorial+1)

theorem bounded_orbit_nilpotent_core_generation
    (hKP : KovacsPraegerAbelianizationBound)
    {C b : ℕ} (G : Subgroup (PermutationGroup b)) [IsSolvable G]
    (hG : OrbitCutoffFamilies.OrbitCutoff C G) :
    ∃ (K : Subgroup G) (S : Finset G), Group.IsNilpotent K ∧
      S.card≤nilpotentControlCutoff C*Nat.sqrt (2*b) ∧
      Subgroup.closure ((S : Set G)∪K)=⊤ :=
  bounded_nilpotent_core_generation C.factorial C.factorial (2*b)
    (bounded_height publishedSolubleSubdirectHeight G hG)
    (boundedChiefSections_of_orbitCutoff G hG)
    (AbelianSectionSize.SectionOmegaBound.of_permutationGroup hKP G)

/-- The existing fixed-cutoff tuple analysis applies after replacing its
cutoff constant by this larger fixed constant. The original group and its
nilpotent-count family remain on the original physical cutoff. -/
theorem bounded_orbit_nilpotent_core_generation_real
    (hKP : KovacsPraegerAbelianizationBound)
    {C b : ℕ} (G : Subgroup (PermutationGroup b)) [IsSolvable G]
    (hG : OrbitCutoffFamilies.OrbitCutoff C G) :
    ∃ (K : Subgroup G) (S : Finset G), Group.IsNilpotent K ∧
      (S.card : ℝ)≤4*((nilpotentControlCutoff C).factorial : ℝ)*Real.sqrt (2*b : ℕ) ∧
      Subgroup.closure ((S : Set G)∪K)=⊤ := by
  obtain ⟨K,S,hK,hS,hgen⟩ := bounded_orbit_nilpotent_core_generation hKP G hG
  refine ⟨K,S,hK,?_,hgen⟩
  have hnat : (S.card : ℝ)≤(nilpotentControlCutoff C : ℝ)*(Nat.sqrt (2*b) : ℝ) := by
    exact_mod_cast hS
  have hsqrt : (Nat.sqrt (2*b) : ℝ)≤Real.sqrt (2*b : ℕ) := by
    apply (Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr
    rw [pow_two]
    exact_mod_cast Nat.sqrt_le (2*b)
  have hcoef : (nilpotentControlCutoff C : ℝ)≤
      4*((nilpotentControlCutoff C).factorial : ℝ) := by
    have h := Nat.self_le_factorial (nilpotentControlCutoff C)
    have hc : (nilpotentControlCutoff C : ℝ)≤((nilpotentControlCutoff C).factorial : ℝ) := by
      exact_mod_cast h
    have hnonneg : (0 : ℝ)≤((nilpotentControlCutoff C).factorial : ℝ) := Nat.cast_nonneg _
    nlinarith
  exact hnat.trans (mul_le_mul hcoef hsqrt (Nat.cast_nonneg _) (by positivity))

end SymmetricSubgroupAsymptotics.MarkedC4.OrdinaryNilpotentGeneration
