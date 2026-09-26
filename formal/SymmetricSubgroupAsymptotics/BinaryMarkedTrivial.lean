import SymmetricSubgroupAsymptotics.BinaryMarkedGoursatPeel
import Mathlib.Algebra.Group.PUnit

/-! The exact base mark for a trivial original group. All three invariants
vanish on the same group, including the actual terminal inflation kernel.
No word-product definition or finite-group recognition is assumed. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

theorem primeCharacters_subsingleton_of_subsingleton (p : ℕ) [Fact p.Prime]
    (G : Type*) [Group G] [Subsingleton G] : Subsingleton (PrimeCharacters p G) := by
  have hz (χ : PrimeCharacters p G) : χ = 0 := by
    ext g
    have hg : g = (0 : Additive G) := Subsingleton.elim _ _
    rw [hg]
    exact χ.map_zero
  exact ⟨fun χ ψ => (hz χ).trans (hz ψ).symm⟩

theorem primeCharacterRank_eq_zero_of_subsingleton (p : ℕ) [Fact p.Prime]
    (G : Type*) [Group G] [Subsingleton G] :
    Module.finrank (ZMod p) (PrimeCharacters p G) = 0 := by
  letI := primeCharacters_subsingleton_of_subsingleton p G
  exact Module.finrank_zero_of_subsingleton

theorem primeRelativeHead_eq_zero_of_subsingleton (p : ℕ) [Fact p.Prime]
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal] [Subsingleton N] :
    Module.finrank (ZMod p) (primeRelativeCharacters p N) = 0 := by
  letI := primeCharacters_subsingleton_of_subsingleton p N
  exact Module.finrank_zero_of_subsingleton

theorem primeDerivedNormalRank_eq_zero_of_subsingleton (p : ℕ) [Fact p.Prime]
    (G : Type*) [Group G] [Finite G] [Subsingleton G] :
    primeDerivedNormalRank p G = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply (primeNormalHeadMax_le_iff p (commutator G) 0).mpr
  intro N _ _
  exact (primeRelativeHead_eq_zero_of_subsingleton p N).le

theorem terminalRestrictedInflationKernel_finrank_eq_zero_of_subsingleton
    (G : Type) [Group G] [Finite G] [Subsingleton G] :
    Module.finrank (ZMod 2) (terminalRestrictedInflationKernel G) = 0 := by
  rw [terminalRestrictedInflationKernel_finrank_eq_primeRelativeHead G]
  exact primeRelativeHead_eq_zero_of_subsingleton 2 _

namespace BinaryMarkedGoursatPeel

theorem exponent_eq_zero_of_subsingleton (G : Type)
    [Group G] [Finite G] [Subsingleton G] (x y z : ℝ) : exponent G x y z = 0 := by
  have hd : binaryCharacterRank G = 0 := primeCharacterRank_eq_zero_of_subsingleton 2 G
  unfold exponent
  rw [hd, primeDerivedNormalRank_eq_zero_of_subsingleton 2 G,
    terminalRestrictedInflationKernel_finrank_eq_zero_of_subsingleton G]
  simp

theorem mark_eq_one_of_subsingleton (G : Type)
    [Group G] [Finite G] [Subsingleton G] (x y z : ℝ) : mark G x y z = 1 := by
  unfold mark
  rw [exponent_eq_zero_of_subsingleton G x y z, Real.rpow_zero]

theorem mark_PUnit (x y z : ℝ) : mark PUnit x y z = 1 :=
  mark_eq_one_of_subsingleton PUnit x y z

end BinaryMarkedGoursatPeel
end SymmetricSubgroupAsymptotics
