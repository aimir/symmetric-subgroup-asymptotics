import SymmetricSubgroupAsymptotics.DerivedInvolutionCosetOrdinaryGenerators
import Mathlib.GroupTheory.Abelianization.Defs

/-! Normalize a genuine ambient generating family into the ACTUAL derived
group using one involution and its literal abelianization exponents.
The resulting two-conjugate Schreier family has twice the original
family size. No index/splitting/finite-ambient/simple/head bound is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.DerivedNormalizedInvolutionFamily
variable {G ι : Type*} [Group G]

/-- A displayed derived element, not merely a normal generator. -/
def normalized (f : ι → G) (r : G) (length : ι → ℕ) (hr : r^2 = 1)
    (hA : ∀ i, Abelianization.of (f i) = (Abelianization.of r)^(length i))
    (i : ι) : commutator G := by
  refine ⟨f i*r^(length i),?_⟩
  rw [← Abelianization.ker_of G]
  change Abelianization.of (f i*r^(length i)) = 1
  rw [map_mul,map_pow,hA,← pow_add]
  have hrA : (Abelianization.of r)^2 = 1 := by rw [← map_pow,hr,map_one]
  rw [← two_mul,pow_mul,hrA,one_pow]

/-- The normalization retains exactly the same ambient source group. -/
theorem normalized_generate (f : ι → G) (r : G) (length : ι → ℕ) (hr : r^2 = 1)
    (hA : ∀ i, Abelianization.of (f i) = (Abelianization.of r)^(length i))
    (hgen : Subgroup.closure (Set.range f ∪ {r}) = ⊤) :
    Subgroup.closure (Set.range (fun i => (normalized f r length hr hA i : G)) ∪ {r}) = ⊤ := by
  let H := Subgroup.closure (Set.range (fun i => (normalized f r length hr hA i : G)) ∪ {r})
  have hrH : r ∈ H := Subgroup.subset_closure (Or.inr rfl)
  have hfH (i : ι) : f i ∈ H := by
    have hn : (normalized f r length hr hA i : G) ∈ H :=
      Subgroup.subset_closure (Or.inl ⟨i,rfl⟩)
    have hh := H.mul_mem hn (H.inv_mem (H.pow_mem hrH (length i)))
    change (f i*r^(length i))*(r^(length i))⁻¹ ∈ H at hh
    simpa only [mul_inv_cancel_right] using hh
  apply top_unique
  rw [← hgen]
  apply (Subgroup.closure_le _).mpr
  intro x hx
  rcases hx with ⟨i,rfl⟩ | hx
  · exact hfH i
  · have hx : x = r := hx
    subst x
    exact hrH

theorem exists_generating_finset [Finite ι]
    (f : ι → G) (r : G) (length : ι → ℕ) (hr : r^2 = 1)
    (hA : ∀ i, Abelianization.of (f i) = (Abelianization.of r)^(length i))
    (hgen : Subgroup.closure (Set.range f ∪ {r}) = ⊤) :
    ∃ S : Finset (commutator G), Subgroup.closure (S : Set (commutator G)) = ⊤ ∧
      S.card ≤ 2*Nat.card ι := by
  exact DerivedInvolutionCosetOrdinaryGenerators.exists_generating_finset
    (normalized f r length hr hA) r (normalized_generate f r length hr hA hgen) hr

end SymmetricSubgroupAsymptotics.DerivedNormalizedInvolutionFamily
