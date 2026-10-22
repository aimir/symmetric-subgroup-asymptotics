import SymmetricSubgroupAsymptotics.CFSGParityEnergyEight
import SymmetricSubgroupAsymptotics.CFSGIntegralGramRootFiniteness
import SymmetricSubgroupAsymptotics.CFSGNormTwoRootPairing

/-! An actual rectangular integral Gram factor with common row parity
embeds its norm-two roots into the explicit energy-eight candidate type.
Positive definiteness supplies injectivity; no root enumeration occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGIntegralGramParityRootCount
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGIntegralGramRootFiniteness CFSGParityEnergyEight
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem mulVec_common_parity (T : Matrix (Fin 8) n ℤ) (j₀ : n)
    (hT : ∀i j,T i j%2=if j=j₀ then 1 else 0) (x : n→ℤ) (i : Fin 8) :
    (T*ᵥx) i%2=x j₀%2 := by
  change (∑j,T i j*x j)%2=x j₀%2
  rw [Finset.sum_int_mod]
  have hterm (j : n) : (T i j*x j)%2=if j=j₀ then x j₀%2 else 0 := by
    rw [Int.mul_emod,hT]
    by_cases hj : j=j₀
    · subst j
      simp
    · simp [hj]
  simp only [hterm]
  simp

def rootCandidate (A : Matrix n n ℤ) (T : Matrix (Fin 8) n ℤ)
    (hg : T.transpose*T=(4:ℤ) • A) (j₀ : n)
    (hT : ∀i j,T i j%2=if j=j₀ then 1 else 0) (x : Roots A) : Candidate := by
  refine ⟨T*ᵥx.val,?_,?_⟩
  · rw [gram_energy A T 4 hg x.val,x.property]
    norm_num
  · have hnonneg : 0≤x.val j₀%2 := Int.emod_nonneg _ (by decide)
    have hlt : x.val j₀%2<2 := Int.emod_lt_of_pos _ (by decide)
    by_cases hz : x.val j₀%2=0
    · exact ⟨false,fun i=>(mulVec_common_parity T j₀ hT x.val i).trans hz⟩
    · have ho : x.val j₀%2=1 := by omega
      exact ⟨true,fun i=>(mulVec_common_parity T j₀ hT x.val i).trans ho⟩

theorem roots_card_le (A : Matrix n n ℤ) (hp : (rationalMatrix A).PosDef)
    (T : Matrix (Fin 8) n ℤ) (hg : T.transpose*T=(4:ℤ) • A) (j₀ : n)
    (hT : ∀i j,T i j%2=if j=j₀ then 1 else 0) : Nat.card (Roots A)≤512 := by
  have hinj : Function.Injective (rootCandidate A T hg j₀ hT) := by
    intro x y he
    apply Subtype.ext
    exact gram_mulVec_injective A T 4 (by decide) hg hp
      (congrArg (fun c : Candidate=>c.val) he)
  exact (Nat.card_le_card_of_injective (rootCandidate A T hg j₀ hT) hinj).trans candidate_card_le

end SymmetricSubgroupAsymptotics.CFSGIntegralGramParityRootCount
