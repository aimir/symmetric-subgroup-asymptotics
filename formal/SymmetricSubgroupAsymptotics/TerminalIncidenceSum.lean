import SymmetricSubgroupAsymptotics.TerminalIncidenceCritical
import SymmetricSubgroupAsymptotics.TerminalFibreCount
import SymmetricSubgroupAsymptotics.BinaryRankSums

/-! Exact central weights and their complete ordered-incidence sum. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics

attribute [local instance] Fintype.ofFinite

local instance {D F : Type*} [AddCommGroup D] [Module (ZMod 2) D]
    [AddCommGroup F] [Module (ZMod 2) F] [Finite D] [Finite F] :
    Finite (D →ₗ[ZMod 2] F) :=
  Finite.of_injective DFunLike.coe DFunLike.coe_injective

variable {ι : Type} [Fintype ι]

/-- The exact kernel-dual reindexing preserves every original annihilator
and every central-fibre exponent. -/
theorem terminal_annihilator_weight_reindex
    (S : Submodule (ZMod 2) (Module.Dual (ZMod 2) (ι → ZMod 2))) (k : ℕ) :
    (∑ L : {L : Submodule (ZMod 2) (Module.Dual (ZMod 2) (ι → ZMod 2)) // L ≤ S},
      (2 : ℝ)^(k*Module.finrank (ZMod 2) L.1)) =
      ∑ B : Submodule (ZMod 2) (ι → ZMod 2),
        if B ≤ S.map binaryDualCoordinates.toLinearMap then
          (2 : ℝ)^(k*Module.finrank (ZMod 2) B) else 0 := by
  let e := Submodule.orderIsoMapComap (binaryDualCoordinates (ι := ι))
  let eS : {L : Submodule (ZMod 2) (Module.Dual (ZMod 2) (ι → ZMod 2)) // L ≤ S} ≃
      {B : Submodule (ZMod 2) (ι → ZMod 2) // B ≤ e S} :=
    Equiv.subtypeEquiv e.toEquiv (fun L => e.le_iff_le.symm)
  calc
    _ = ∑ B : {B : Submodule (ZMod 2) (ι → ZMod 2) // B ≤ e S},
        (2 : ℝ)^(k*Module.finrank (ZMod 2) B.1) := by
      apply Fintype.sum_equiv eS
      intro L
      rw [(binaryDualCoordinates.submoduleMap L.1).finrank_eq]
      rfl
    _ = _ := by
      simp only [← Finset.sum_filter]
      symm
      exact Finset.sum_subtype (Finset.univ.filter (fun B => B ≤ e S))
        (fun _ => by simp) (fun B => (2 : ℝ)^(k*Module.finrank (ZMod 2) B))

/-- The complete elementary quotient map of the actual exterior. -/
abbrev terminalExteriorMap (T : Type) [Group T] : T →* Multiplicative (BinaryAbelianization T) :=
  AddMonoidHom.toMultiplicativeRight (binaryAbelianizationMap T)

/-- The literal central-fibre weight, retaining the original relation subspace. -/
def terminalCriticalMapWeight (a : ℕ) (s : ι → Bool) (u : ℕ) (T : Type) [Group T]
    (p : ((Fin u → ZMod 2) × BinaryAbelianization T) →ₗ[ZMod 2] CriticalProductSpace a s) : ℝ :=
  ∑ B : Submodule (ZMod 2) (ι → ZMod 2),
    if B ≤ terminalCriticalRecordAnnihilator a s (terminalExteriorMap T) p then
      (2 : ℝ)^((u+binaryCharacterRank T)*Module.finrank (ZMod 2) B) else 0

theorem terminalCriticalMapWeight_nonneg (a : ℕ) (s : ι → Bool) (u : ℕ)
    (T : Type) [Group T] (p) : 0 ≤ terminalCriticalMapWeight a s u T p := by
  apply Finset.sum_nonneg
  intro B _
  split_ifs <;> positivity

/-- All literal ordered maps, onto every original nonabelian quotient
coordinate, carry their exact original central-fibre weights. -/
def terminalCriticalWeightedMaps (a : ℕ) (s : ι → Bool) (u : ℕ)
    (T : Type) [Group T] [Finite T] : ℝ :=
  ∑ p : ((Fin u → ZMod 2) × BinaryAbelianization T) →ₗ[ZMod 2] CriticalProductSpace a s,
    if ∀ i, Function.Surjective (fun x => (p x).2 i) then
      terminalCriticalMapWeight a s u T p else 0

private theorem terminal_sum_indicator_card {X : Type*} [Fintype X]
    (P : X → Prop) [DecidablePred P] (z : ℝ) :
    (∑ x, if P x then z else 0) = (Nat.card {x // P x} : ℝ)*z := by
  simp only [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,
    Nat.card_eq_fintype_card,Fintype.card_subtype]

/-- Interchanging the original ordered-map and relation-subspace sums is
an equality, before dimensions or realization bounds replace anything. -/
theorem terminalCriticalWeightedMaps_eq (a : ℕ) (s : ι → Bool) (u : ℕ)
    (T : Type) [Group T] [Finite T] :
    terminalCriticalWeightedMaps a s u T =
      ∑ B : Submodule (ZMod 2) (ι → ZMod 2),
        (Nat.card (TerminalCriticalRecordMaps (U := Fin u → ZMod 2) a s
          (terminalExteriorMap T) B) : ℝ) *
            (2 : ℝ)^((u+binaryCharacterRank T)*Module.finrank (ZMod 2) B) := by
  unfold terminalCriticalWeightedMaps terminalCriticalMapWeight
  calc
    _ = ∑ p : ((Fin u → ZMod 2) × BinaryAbelianization T) →ₗ[ZMod 2] CriticalProductSpace a s,
        ∑ B : Submodule (ZMod 2) (ι → ZMod 2),
          if (∀ i, Function.Surjective (fun x => (p x).2 i)) ∧
            B ≤ terminalCriticalRecordAnnihilator a s (terminalExteriorMap T) p then
              (2 : ℝ)^((u+binaryCharacterRank T)*Module.finrank (ZMod 2) B) else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      split_ifs with hp
      · simp [hp]
      · simp only [hp,false_and,ite_false,Finset.sum_const_zero]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro B _
      simpa only [TerminalCriticalRecordMaps] using terminal_sum_indicator_card
        (fun p : ((Fin u → ZMod 2) × BinaryAbelianization T) →ₗ[ZMod 2] CriticalProductSpace a s =>
          (∀ i, Function.Surjective (fun x => (p x).2 i)) ∧
            B ≤ terminalCriticalRecordAnnihilator a s (terminalExteriorMap T) p)
        ((2 : ℝ)^((u+binaryCharacterRank T)*Module.finrank (ZMod 2) B))

/-- Full rank-binned ordered-incidence estimate, retaining the ell=0 fibre
and the complete u+d₂(T) central lift weight. -/
theorem terminalCriticalWeightedMaps_le (a : ℕ) (s : ι → Bool) (u : ℕ)
    (T : Type) [Group T] [Finite T] :
    terminalCriticalWeightedMaps a s u T ≤
      ∑ l ∈ Finset.range (Fintype.card ι+1), (binaryGaussianCoefficient (Fintype.card ι) l : ℝ) *
        ((72 : ℝ)*2^Module.finrank (ZMod 2) (terminalRestrictedInflationKernel T))^l *
          2^((u+binaryCharacterRank T)*(criticalProductRank a s-2*l)) *
            2^((u+binaryCharacterRank T)*l) := by
  rw [terminalCriticalWeightedMaps_eq]
  calc
    _ ≤ ∑ B : Submodule (ZMod 2) (ι → ZMod 2),
        ((72 : ℝ)*2^Module.finrank (ZMod 2) (terminalRestrictedInflationKernel T))^
          Module.finrank (ZMod 2) B *
        2^((u+binaryCharacterRank T)*(criticalProductRank a s-2*Module.finrank (ZMod 2) B)) *
          2^((u+binaryCharacterRank T)*Module.finrank (ZMod 2) B) := by
      apply Finset.sum_le_sum
      intro B _
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have h := terminalCriticalRecordMaps_canonical_count_le (U := Fin u → ZMod 2) (T := T) a s B
      simp only [Module.finrank_pi,Fintype.card_fin] at h
      exact_mod_cast h
    _ = _ := by
      rw [binary_subspace_sum_by_rank]
      simp only [Module.finrank_pi]
      apply Finset.sum_congr rfl
      intro l hl
      have hr (B : {B : Submodule (ZMod 2) (ι → ZMod 2) // Module.finrank (ZMod 2) B=l}) :
          Module.finrank (ZMod 2) B.1=l := B.2
      simp only [hr,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
        ← Nat.card_eq_fintype_card]
      rw [binary_subspace_rank_card (V := ι → ZMod 2) l (by simpa using hl)]
      simp only [Module.finrank_pi,Nat.card_eq_fintype_card]
      ring

end SymmetricSubgroupAsymptotics
