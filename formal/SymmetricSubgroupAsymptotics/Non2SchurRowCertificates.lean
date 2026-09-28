import SymmetricSubgroupAsymptotics.Non2SchurRowProfile
import SymmetricSubgroupAsymptotics.Non2CoupledSchurNumerics

/-!
# Structural certificates for actual nonfixed Schur rows

The exact Schur profile converts the four integer branch conditions on an
actual simple row into the real certificates consumed by the coupled
capacity theorem.  What remains after this file is to prove that every
nonfixed simple row satisfies one of these four structural branches.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

universe u
variable {k B A : Type u} [Field k] [Group B]
    [AddCommGroup A] [Module k A]

/-- The four integer structural alternatives for an actual simple row.
`L` and `q` are not supplied: they are the mixed socle dimension and the
exact Schur product degree defined from that row. -/
def Non2SchurStructuralBranch
    [FiniteDimensional k A]
    (σ : Representation k B A) (S : Submodule k[B] σ.asModule)
    [IsSimpleModule k[B] S] (s t : Nat) : Prop :=
  let L := schurMixedSocleDimension σ S t
  let q := schurSimpleProductDegree σ S
  (32 * t ≤ 11 * s ∧ 2 * L ≤ s ∧ 3 ≤ q) ∨
  (8 * L ≤ 3 * s ∧ q = 2) ∨
  (5 * t ≤ s ∧ L ≤ s ∧ q = 8) ∨
  (32 * t ≤ 11 * s ∧ L ≤ s ∧ 9 ≤ q)

/-- Every proved structural branch becomes one of the four checked
coupled-row certificates for the actual intrinsic Hom density. -/
theorem Non2SchurStructuralBranch.rowCertificate
    [FiniteDimensional k A]
    (σ : Representation k B A) (S : Submodule k[B] σ.asModule)
    [IsSimpleModule k[B] S] (s t : Nat)
    (hbranch : Non2SchurStructuralBranch σ S s t) :
    Non2CoupledRowCertificate (s : ℝ) (t : ℝ)
      ((Module.finrank k (S →ₗ[k[B]] σ.asModule) : ℝ) /
        Module.finrank k S) := by
  let L := schurMixedSocleDimension σ S t
  let q := schurSimpleProductDegree σ S
  let r := (Module.finrank k (S →ₗ[k[B]] σ.asModule) : ℝ) /
    Module.finrank k S
  have hprofile : (q : ℝ) * r = (L : ℝ) - t :=
    schurSimpleProductDegree_mul_ratio σ S t
  have hr : 0 ≤ r := schurSimpleRatio_nonneg σ S
  change (32 * t ≤ 11 * s ∧ 2 * L ≤ s ∧ 3 ≤ q) ∨
    (8 * L ≤ 3 * s ∧ q = 2) ∨
    (5 * t ≤ s ∧ L ≤ s ∧ q = 8) ∨
    (32 * t ≤ 11 * s ∧ L ≤ s ∧ 9 ≤ q) at hbranch
  rcases hbranch with ⟨ht, hL, hq⟩ | ⟨hL, hq⟩ |
      ⟨ht, hL, hq⟩ | ⟨ht, hL, hq⟩
  · left
    refine ⟨(L : ℝ), ?_, ?_, ?_⟩
    · have htR : 32 * (t : ℝ) ≤ 11 * (s : ℝ) := by exact_mod_cast ht
      linarith
    · have hLR : 2 * (L : ℝ) ≤ (s : ℝ) := by exact_mod_cast hL
      linarith
    · have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
      nlinarith
  · right; left
    refine ⟨(L : ℝ), ?_, ?_⟩
    · have hLR : 8 * (L : ℝ) ≤ 3 * (s : ℝ) := by exact_mod_cast hL
      linarith
    · have hqR : (q : ℝ) = 2 := by exact_mod_cast hq
      nlinarith
  · right; right; left
    refine ⟨(L : ℝ), ?_, ?_, ?_⟩
    · have htR : 5 * (t : ℝ) ≤ (s : ℝ) := by exact_mod_cast ht
      linarith
    · exact_mod_cast hL
    · have hqR : (q : ℝ) = 8 := by exact_mod_cast hq
      nlinarith
  · right; right; right
    refine ⟨(L : ℝ), ?_, ?_, ?_⟩
    · have htR : 32 * (t : ℝ) ≤ 11 * (s : ℝ) := by exact_mod_cast ht
      linarith
    · exact_mod_cast hL
    · have hqR : (9 : ℝ) ≤ q := by exact_mod_cast hq
      nlinarith

end SymmetricSubgroupAsymptotics

end
