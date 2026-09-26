import SymmetricSubgroupAsymptotics.BinaryOrderCharacterFusion
import SymmetricSubgroupAsymptotics.FusionDirectPhysicalUnion
import SymmetricSubgroupAsymptotics.FusionDirectDecay

/-!
# Direct contractive fusion for complete order/character selections

Every selected prefix is even and strictly shorter than its original
positive width. The first moment therefore gives an actual forward row,
and its original weighted aggregate decays without a coarse subgroup-count
input. The character class-count input remains explicit in the physical
counting theorem. No global physical cover is manufactured here.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- Exponential aggregate decay for the exact direct row, once its
markers are even and strictly shorter than the original widths. -/
theorem fusionFiniteDirectRow_decay {ι : Type*} [Fintype ι]
    (h v r : ι → ℕ) (D a e : ι → ℝ)
    (hv : ∀ i, v i < 2*h i) (hvr : ∀ i, v i = 2*r i)
    (hD : ∀ i, 0≤D i) (ha : ∀ i, 0<a i) (he : ∀ i, 0<e i) :
    ∃ C κ : ℝ, 0<C ∧ 0<κ ∧ ∀ᶠ n : ℕ in atTop,
      ∑ m ∈ Finset.range n, fusionFiniteDirectRow h v D a e n m ≤
        C*(2:ℝ)^(-κ*(n:ℝ)) := by
  have hr : ∀ i, r i≤h i := by
    intro i
    have := hv i
    have := hvr i
    omega
  obtain ⟨C,κ,hC,hκ,hbound⟩ :=
    fusionDirectKernel_shifted_finite_sum h r D a e hr hD ha he
  refine ⟨C,κ,hC,hκ,?_⟩
  filter_upwards [hbound,
    Filter.eventually_all.mpr (fun i => eventually_ge_atTop (2*h i))] with n hn hw
  have hid := fusionFiniteDirectRow_weighted_sum h v D a e hv (fun _ => 1) n hw
  have hb : (∑ i, fusionDirectKernel (n-2*h i) (h i) (v i) (D i) (a i) (e i)) ≤
      C*(2:ℝ)^(-κ*(n:ℝ)) := by simpa only [hvr] using hn
  simpa only [mul_one] using hid.le.trans (by simpa only [mul_one] using hb)

/-- In particular the complete original direct row is eventually
contractive before any bound on the unknown total subgroup sequence. -/
theorem fusionFiniteDirectRow_contractive {ι : Type*} [Fintype ι]
    (h v r : ι → ℕ) (D a e : ι → ℝ)
    (hv : ∀ i, v i < 2*h i) (hvr : ∀ i, v i = 2*r i)
    (hD : ∀ i, 0≤D i) (ha : ∀ i, 0<a i) (he : ∀ i, 0<e i) :
    ∀ᶠ n : ℕ in atTop,
      ∑ m ∈ Finset.range n, fusionFiniteDirectRow h v D a e n m ≤ 1/2 := by
  obtain ⟨C,κ,hC,hκ,hbound⟩ := fusionFiniteDirectRow_decay h v r D a e hv hvr hD ha he
  filter_upwards [hbound, eventually_exponential_le_inv_rpow hκ 1,
    eventually_ge_atTop (max 1 ⌈2*C⌉₊)] with n hn hexp hlarge
  have hn1 : 1≤n := (le_max_left _ _).trans hlarge
  have hnpos : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hnC : 2*C≤(n:ℝ) := (Nat.le_ceil (2*C)).trans
    (by exact_mod_cast (le_max_right _ _).trans hlarge)
  rw [Real.rpow_one] at hexp
  apply hn.trans ((mul_le_mul_of_nonneg_left hexp hC.le).trans ?_)
  rw [mul_one_div]
  exact (div_le_iff₀ hnpos).mpr (by linarith)

namespace BinaryOrderCharacterCertificate

variable {w : ℕ} {U : Subgroup (Equiv.Perm (Fin w))} {N : Subgroup U} [N.Normal]

/-- Both existing certificate alternatives have an even marker. -/
def markerHalf (C : BinaryOrderCharacterCertificate U N) : ℕ :=
  match C with
  | .inl _ => Nat.log 2 (Nat.card (U ⧸ N))
  | .inr _ => 0

theorem prefixDegree_eq_two_mul_markerHalf (C : BinaryOrderCharacterCertificate U N) :
    C.prefixDegree = 2*C.markerHalf := by
  cases C <;> rfl

theorem prefixDegree_lt (C : BinaryOrderCharacterCertificate U N) (hw : 0<w) :
    C.prefixDegree < w := by
  cases C with
  | inl B => exact B.gap
  | inr B => exact hw

end BinaryOrderCharacterCertificate

namespace BinaryOrderCharacterSelection

variable {h : ℕ} {U : Subgroup (Equiv.Perm (Fin (2*h)))}
    (C : BinaryOrderCharacterSelection U)

/-- The existing exact first moment supplies the direct actual bound;
the original character class-count hypothesis is retained. -/
theorem direct_physical_bound (hMaroti : NilpotentConjugacyClassInput)
    (hU : IsPGroup 2 U) (b : ℕ)
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop) (hP : FusionOrbitNatural U P) :
    (Nat.card (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) : ℝ) /
      exactBenchmark (b+2*h) ≤
      ∑ N : {N : Subgroup U // N.Normal},
        fusionDirectKernel b h (C.prefixDegree N) (C.liftConstant N)
          (Nat.card (Subgroup.normalizer (U : Set (Equiv.Perm (Fin (2*h))))) : ℝ)
          (C.gapParameter N) *
          ((subgroupCount (b+C.prefixDegree N) : ℝ)/exactBenchmark (b+C.prefixDegree N)) :=
  fusionPhysical_direct_bound U b P hP C.prefixDegree C.liftConstant C.gapParameter
    (fun N J => C.momentWeight N J) C.liftConstant_nonneg
    (C.original_envelope hMaroti hU b P)
    (fun N => by simpa only [pow_one, one_mul] using C.momentWeight_moment_le N b 1)

end BinaryOrderCharacterSelection

section Menu

variable {ι : Type*} [Fintype ι] (h : ι → ℕ)
    (U : ∀ i, Subgroup (Equiv.Perm (Fin (2*h i))))
    (C : ∀ i, BinaryOrderCharacterSelection (U i))

/-- The actual original-action/normal sum, installed in its shifted row. -/
def binaryOrderCharacterDirectRow (n m : ℕ) : ℝ :=
  fusionPhysicalDirectRow h U (fun i => (C i).prefixDegree)
    (fun i => (C i).liftConstant) (fun i => (C i).gapParameter) n m

theorem binaryOrderCharacterDirectRow_nonneg (n m : ℕ) :
    0≤binaryOrderCharacterDirectRow h U C n m :=
  fusionPhysicalDirectRow_nonneg h U _ _ _ (fun i => (C i).liftConstant_nonneg) n m

theorem binaryOrderCharacterDirectRow_forward (hh : ∀ i, 0<h i)
    {n m : ℕ} (hnm : n ≤ m) : binaryOrderCharacterDirectRow h U C n m = 0 :=
  fusionPhysicalDirectRow_forward h U _ _ _
    (fun i N => (C i N).prefixDegree_lt (by have := hh i; omega)) hnm

/-- Complete original physical coverage gives a forward first-moment
recurrence with no additive hot error and no coarse-growth hypothesis. -/
theorem binaryOrderCharacterSelection_direct_recurrence
    (hMaroti : NilpotentConjugacyClassInput) (hU : ∀ i, IsPGroup 2 (U i))
    (hh : ∀ i, 0<h i) (n : ℕ) (hn : ∀ i, 2*h i≤n)
    (F : Set (Subgroup (Equiv.Perm (Fin n))))
    (P : ∀ i, Subgroup (U i × Equiv.Perm (Fin (n-2*h i))) → Prop)
    (hP : ∀ i, FusionOrbitNatural (U i) (P i))
    (hcover : ∀ H∈F, ∃ i, H∈FusionCanonicalFamily (U i) (hn i) (P i)) :
    (Nat.card F : ℝ)/exactBenchmark n ≤
      ∑ m ∈ Finset.range n, binaryOrderCharacterDirectRow h U C n m *
        ((subgroupCount m : ℝ)/exactBenchmark m) :=
  fusionPhysicalUnion_direct_recurrence h U n hn F P hP hcover
    (fun i => (C i).prefixDegree) (fun i => (C i).liftConstant)
    (fun i => (C i).gapParameter) (fun i N J => (C i).momentWeight N J)
    (fun i N => (C i N).prefixDegree_lt (by have := hh i; omega))
    (fun i => (C i).liftConstant_nonneg)
    (fun i => (C i).original_envelope hMaroti (hU i) (n-2*h i) (P i))
    (fun i N => by simpa only [pow_one, one_mul] using
      (C i).momentWeight_moment_le N (n-2*h i) 1)

/-- The complete original weighted direct row has a positive exponential
rate. Its proof does not assume the character class bound or total counts. -/
theorem binaryOrderCharacterDirectRow_decay (hh : ∀ i, 0<h i) :
    ∃ A κ : ℝ, 0<A ∧ 0<κ ∧ ∀ᶠ n : ℕ in atTop,
      ∑ m ∈ Finset.range n, binaryOrderCharacterDirectRow h U C n m ≤
        A*(2:ℝ)^(-κ*(n:ℝ)) :=
  fusionFiniteDirectRow_decay
    (fun j : FusionPhysicalMenuAxis h U => h j.1)
    (fun j => (C j.1).prefixDegree j.2) (fun j => (C j.1 j.2).markerHalf)
    (fun j => (C j.1).liftConstant j.2) (fun j => fusionPhysicalMenuDivisor h U j.1)
    (fun j => (C j.1).gapParameter j.2)
    (fun j => (C j.1 j.2).prefixDegree_lt (by have := hh j.1; omega))
    (fun j => (C j.1 j.2).prefixDegree_eq_two_mul_markerHalf)
    (fun j => (C j.1).liftConstant_nonneg j.2)
    (fun j => fusionPhysicalMenuDivisor_pos h U j.1)
    (fun j => (C j.1).gapParameter_pos j.2)

/-- Eventual contraction of the same literal row. -/
theorem binaryOrderCharacterDirectRow_contractive (hh : ∀ i, 0<h i) :
    ∀ᶠ n : ℕ in atTop,
      ∑ m ∈ Finset.range n, binaryOrderCharacterDirectRow h U C n m ≤ 1/2 :=
  fusionFiniteDirectRow_contractive
    (fun j : FusionPhysicalMenuAxis h U => h j.1)
    (fun j => (C j.1).prefixDegree j.2) (fun j => (C j.1 j.2).markerHalf)
    (fun j => (C j.1).liftConstant j.2) (fun j => fusionPhysicalMenuDivisor h U j.1)
    (fun j => (C j.1).gapParameter j.2)
    (fun j => (C j.1 j.2).prefixDegree_lt (by have := hh j.1; omega))
    (fun j => (C j.1 j.2).prefixDegree_eq_two_mul_markerHalf)
    (fun j => (C j.1).liftConstant_nonneg j.2)
    (fun j => fusionPhysicalMenuDivisor_pos h U j.1)
    (fun j => (C j.1).gapParameter_pos j.2)

end Menu
end SymmetricSubgroupAsymptotics

end
