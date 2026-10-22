import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Group.Units.Hom

/-! A genuine coinvariant criterion for literal matrix actions. If the
matrix action is closed under transpose and has no common fixed vector,
its actual differences (g-1)v span the whole vector space. No irreducible
representation or named classical-group theorem is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators Matrix

namespace SymmetricSubgroupAsymptotics.CFSGMatrixMovingSpan
variable {K I G : Type*} [Field K] [Fintype I] [DecidableEq I] [Group G]

def movingSpan (rho : G →* (Matrix I I K)ˣ) : Submodule K (I → K) :=
  Submodule.span K {x | ∃ g : G, ∃ v : I → K, x = (rho g : Matrix I I K) *ᵥ v - v}

theorem movingSpan_eq_top (rho : G →* (Matrix I I K)ˣ)
    (htranspose : ∀ g : G, ∃ h : G, (rho h : Matrix I I K) = (rho g : Matrix I I K).transpose)
    (hfixed : ∀ w : I → K, (∀ g : G, (rho g : Matrix I I K) *ᵥ w = w) → w = 0) :
    movingSpan rho = ⊤ := by
  apply Submodule.dualAnnihilator_eq_bot_iff.mp
  apply bot_unique
  intro f hf
  change f = 0
  have hinv (g : G) (v : I → K) : f ((rho g : Matrix I I K) *ᵥ v) = f v := by
    have hs : (rho g : Matrix I I K) *ᵥ v - v ∈ movingSpan rho :=
      Submodule.subset_span ⟨g, v, rfl⟩
    have hz := (Submodule.mem_dualAnnihilator f).mp hf _ hs
    rw [map_sub, sub_eq_zero] at hz
    exact hz
  let w : I → K := fun i => f (Pi.single i 1)
  have hrep (v : I → K) : f v = dotProduct w v := by
    have hv : (∑ i, v i • (Pi.single i 1 : I → K)) = v := by
      funext j
      simp [Pi.single_apply]
    calc
      f v = f (∑ i, v i • (Pi.single i 1 : I → K)) := congrArg f hv.symm
      _ = ∑ i, v i * w i := by
        simp only [map_sum, map_smul, smul_eq_mul, w]
      _ = dotProduct w v := by
        apply Finset.sum_congr rfl
        intro i _
        exact mul_comm _ _
  have hw : w = 0 := by
    apply hfixed
    intro g
    obtain ⟨h, hh⟩ := htranspose g
    funext j
    have he := hinv h (Pi.single j 1)
    rw [hrep, hrep, Matrix.mulVec_single_one, dotProduct_single_one] at he
    rw [hh] at he
    simpa only [Matrix.mulVec, dotProduct, Matrix.col_apply, Matrix.transpose_apply,
      mul_comm] using he
  apply LinearMap.ext
  intro v
  rw [hrep, hw, zero_dotProduct]
  rfl

end SymmetricSubgroupAsymptotics.CFSGMatrixMovingSpan
