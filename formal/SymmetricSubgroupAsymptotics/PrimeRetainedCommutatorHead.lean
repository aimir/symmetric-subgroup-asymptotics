import SymmetricSubgroupAsymptotics.PrimeRelativeHeadChainCapacity
import SymmetricSubgroupAsymptotics.PrimeRelativeRadicalPresentation
import Mathlib.Data.Nat.Log

/-! Retained characters on an original normal chain annihilate its actual
mixed commutators. This gives a kernel-dimension bound that can be checked
by matrices without declaring that all invariant characters extend.
The quotient and every conjugating element remain those of the original
ambient group. No splitting, p-group hypothesis or finite menu is used.
-/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics

variable {G : Type*} [Group G]
variable (B N : Subgroup G) [B.Normal] [N.Normal]
variable (p : ℕ) [Fact p.Prime]

/-- The same mixed commutator viewed inside the original lower subgroup. -/
def normalChainMixedCommutator (hcomm : ⁅N, (⊤ : Subgroup G)⁆ ≤ B)
    (n : N) (g : G) : B :=
  ⟨⁅(n : G), g⁆, hcomm
    (Subgroup.commutator_mem_commutator n.2 (Subgroup.mem_top g))⟩

/-- Necessary commutator equations on actual whole-ambient B characters.
These equations are not asserted to characterize extendibility. -/
def normalChainMixedAnnihilator (hcomm : ⁅N, (⊤ : Subgroup G)⁆ ≤ B) :
    Submodule (ZMod p) (primeRelativeCharacters p B) where
  carrier := {χ | ∀ n : N, ∀ g : G,
    χ.1 (Additive.ofMul (normalChainMixedCommutator B N hcomm n g)) = 0}
  zero_mem' := by intro n g; rfl
  add_mem' := by
    intro χ ψ hχ hψ n g
    change χ.1 _ + ψ.1 _ = 0
    rw [hχ, hψ, add_zero]
  smul_mem' := by
    intro c χ hχ n g
    change c • χ.1 _ = 0
    rw [hχ, smul_zero]

/-- The existing chain restriction is evaluation on the same B element
included into N. No kernel equivalence changes the underlying element. -/
theorem normalChainRestriction_apply_original (hBN : B ≤ N)
    (χ : primeActionCharacters p (normalChainSourceAction N)) (b : B) :
    (normalChainRestriction B N p hBN χ).1 (Additive.ofMul b) =
      χ.1 (Additive.ofMul (⟨(b : G), hBN b.2⟩ : N)) := rfl

/-- Every extendible relative character annihilates all original mixed
commutators, including those involving elements outside N. -/
theorem normalChainRetainedCharacters_le_mixedAnnihilator (hBN : B ≤ N)
    (hcomm : ⁅N, (⊤ : Subgroup G)⁆ ≤ B) :
    normalChainRetainedCharacters B N p hBN ≤
      normalChainMixedAnnihilator B N p hcomm := by
  rintro χ ⟨ψ, rfl⟩ n g
  rw [normalChainRestriction_apply_original]
  have hz := (mem_primeRelativeRadical_iff p N ⁅(n : G), g⁆).mp
    (commutator_mem_primeRelativeRadical p N n g)
  exact hz.2 (normalChainSourceCharactersEquiv N p ψ)

/-- The original exact chain identity bounds the head by its same
quotient contribution and the mixed-commutator annihilator. -/
theorem primeRelativeHead_chain_le_mixedAnnihilator [Finite G]
    (hBN : B ≤ N) (hcomm : ⁅N, (⊤ : Subgroup G)⁆ ≤ B) :
    Module.finrank (ZMod p) (primeRelativeCharacters p N) ≤
      Module.finrank (ZMod p) (primeRelativeCharacters p (normalChainQuotient B N)) +
        Module.finrank (ZMod p) (normalChainMixedAnnihilator B N p hcomm) := by
  rw [primeRelativeHead_chain_eq B N p hBN]
  exact Nat.add_le_add_left
    (Submodule.finrank_mono
      (normalChainRetainedCharacters_le_mixedAnnihilator B N p hBN hcomm)) _

/-- A cardinal version requires no elementary-abelian quotient premise.
In the carrier application, this is the actual W=N/G' contribution. -/
theorem primeRelativeHead_chain_le_log_card_add_mixedAnnihilator [Finite G]
    (hBN : B ≤ N) (hcomm : ⁅N, (⊤ : Subgroup G)⁆ ≤ B) :
    Module.finrank (ZMod p) (primeRelativeCharacters p N) ≤
      Nat.log p (Nat.card (normalChainQuotient B N)) +
        Module.finrank (ZMod p) (normalChainMixedAnnihilator B N p hcomm) := by
  have hq : Module.finrank (ZMod p)
      (primeRelativeCharacters p (normalChainQuotient B N)) ≤
      Nat.log p (Nat.card (normalChainQuotient B N)) :=
    (Submodule.finrank_le _).trans
      (Nat.le_log_of_pow_le (Fact.out : p.Prime).one_lt
        (primeCharacters_pow_finrank_le_card p (normalChainQuotient B N)))
  exact (primeRelativeHead_chain_le_mixedAnnihilator B N p hBN hcomm).trans
    (Nat.add_le_add_right hq _)

/-- A finite matrix may evaluate any chosen actual elements of N against
any chosen original conjugators. Fewer tests only enlarge its kernel. -/
def normalChainMixedTestMap {ι κ : Type*}
    (hcomm : ⁅N, (⊤ : Subgroup G)⁆ ≤ B) (x : ι → N) (y : κ → G) :
    primeRelativeCharacters p B →ₗ[ZMod p] (ι × κ → ZMod p) where
  toFun χ ij := χ.1 (Additive.ofMul
    (normalChainMixedCommutator B N hcomm (x ij.1) (y ij.2)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem normalChainMixedAnnihilator_le_test_ker {ι κ : Type*}
    (hcomm : ⁅N, (⊤ : Subgroup G)⁆ ≤ B) (x : ι → N) (y : κ → G) :
    normalChainMixedAnnihilator B N p hcomm ≤
      (normalChainMixedTestMap B N p hcomm x y).ker := by
  intro χ hχ
  apply LinearMap.mem_ker.mpr
  funext ij
  exact hχ (x ij.1) (y ij.2)

/-- Actual matrix-kernel bound; no generating or coverage assertion on
the selected test lists is needed for this upper bound. -/
theorem primeRelativeHead_chain_le_log_card_add_test_ker [Finite G]
    {ι κ : Type*} (hBN : B ≤ N) (hcomm : ⁅N, (⊤ : Subgroup G)⁆ ≤ B)
    (x : ι → N) (y : κ → G) :
    Module.finrank (ZMod p) (primeRelativeCharacters p N) ≤
      Nat.log p (Nat.card (normalChainQuotient B N)) +
        Module.finrank (ZMod p) (normalChainMixedTestMap B N p hcomm x y).ker := by
  exact (primeRelativeHead_chain_le_log_card_add_mixedAnnihilator
    B N p hBN hcomm).trans
      (Nat.add_le_add_left (Submodule.finrank_mono
        (normalChainMixedAnnihilator_le_test_ker B N p hcomm x y)) _)

/-- Above the actual derived subgroup, the mixed-commutator containment
is automatic. No extra nilpotence, evaluation-kernel or square premise
is needed for this generic necessary-character bound. -/
theorem primeRelativeHead_above_derived_le_log_card_add_test_ker [Finite G]
    {ι κ : Type*} (hDN : commutator G ≤ N) (x : ι → N) (y : κ → G) :
    Module.finrank (ZMod p) (primeRelativeCharacters p N) ≤
      Nat.log p (Nat.card (normalChainQuotient (commutator G) N)) +
        Module.finrank (ZMod p)
          (normalChainMixedTestMap (commutator G) N p
            (Subgroup.commutator_mono le_top le_rfl) x y).ker :=
  primeRelativeHead_chain_le_log_card_add_test_ker (commutator G) N p hDN
    (Subgroup.commutator_mono le_top le_rfl) x y

end SymmetricSubgroupAsymptotics
