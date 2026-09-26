import SymmetricSubgroupAsymptotics.PrimeDerivedMixedVanishing
import SymmetricSubgroupAsymptotics.PrimeRelativeVanishingOrder
import SymmetricSubgroupAsymptotics.PrimeDerivedVanishingCenter
import SymmetricSubgroupAsymptotics.StarAlternatingExactDimensions
import SymmetricSubgroupAsymptotics.PrimeRelativeRadicalPresentation
import Lean.Elab.Tactic.Omega

/-! Uniform crossing bounds from the complete actual star family.
The mixed commutator need not equal the derived intersection. Its complete
vanishing space and actual cardinality instead give a head upper bound;
all original power contributions remain in the full relative radical.
Original normal comparability is a separate genuine certificate input. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime] {G : Type*} [Group G] [Finite G]

/-- Original powers can enlarge the radical and improve this inequality.
The full mixed commutator is only used as a proved subgroup of that radical. -/
theorem primeRelativeHead_pow_mul_mixed_card_le (N : Subgroup G) [N.Normal] :
    p ^ Module.finrank (ZMod p) (primeRelativeCharacters p N) *
        Nat.card ↥(⁅N, (⊤ : Subgroup G)⁆) ≤ Nat.card N := by
  have hm : ⁅N, (⊤ : Subgroup G)⁆ ≤ primeRelativeRadical p N :=
    (primeRelativePowerCommutator_commutator_le p N).trans
      (primeRelativePowerCommutator_le_radical p N)
  exact (Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hm)).trans_eq
    (primeRelativeRadical_card_factorization p N).symm

/-- Complete vanishing parameters count the exact original quotient
derived group once the original intersection contains the relative radical. -/
theorem quotientCommutator_card_eq_pow_vanishing
    (N : Subgroup G) [N.Normal]
    (hRB : primeRelativeRadical p (commutator G) ≤ N ⊓ commutator G) :
    Nat.card (commutator (G ⧸ N)) =
      p ^ Module.finrank (ZMod p) (derivedCharactersVanishingOn p (N ⊓ commutator G)) := by
  have hc := quotientCommutator_card_mul_inf N
  have hd : Nat.card (commutator G) =
      p ^ Module.finrank (ZMod p) (derivedCharactersVanishingOn p (N ⊓ commutator G)) *
        Nat.card ↥(N ⊓ commutator G) :=
    primeRelativeVanishing_card_factorization p (commutator G) (N ⊓ commutator G)
      inf_le_right hRB
  exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥(N ⊓ commutator G))) (hc.trans hd)

variable (hker : (primeAbelianizationGroupMap p G).ker = commutator G)
    (hG : IsPGroup p G)
    {U : Type*} [AddCommGroup U] [Module (ZMod p) U] [FiniteDimensional (ZMod p) U]
    (eChars : primeRelativeCharacters p (commutator G) ≃ₗ[ZMod p] Module.Dual (ZMod p) U)
    (eV : PrimeAbelianization p G ≃ₗ[ZMod p] U × ZMod p)
    (hform : ∀ χ x y, derivedEvaluationBilinearMap p hker χ x y =
      starAlternatingFamily (eChars χ) (eV x) (eV y))
include hker hG eChars eV hform

/-- The full mixed-vanishing space has the exact complementary dimension
for a proper original derived intersection; no pair-zero claim is used. -/
theorem starDerived_mixedVanishing_finrank_add_image
    (N : Subgroup G) [N.Normal] (hnotDN : ¬commutator G ≤ N) :
    Module.finrank (ZMod p) (primeDerivedImage p N) +
        Module.finrank (ZMod p) (derivedCharactersVanishingOn p ⁅N, (⊤ : Subgroup G)⁆) =
      Module.finrank (ZMod p) U := by
  have hLB := derivedCharactersVanishingOn_ne_bot_of_lt p hG
    (N ⊓ commutator G) (derivedIntersection_lt_of_not_derived_le N hnotDN)
  have hJ : linearJointAnnihilator (derivedEvaluationBilinearMap p hker)
      (primeDerivedImage p N) ≠ ⊥ := by
    intro hz
    exact hLB (le_antisymm
      ((derivedCharactersVanishingOn_le_joint p hker (N ⊓ commutator G) N le_rfl).trans hz.le)
      bot_le)
  have hd := linearJointAnnihilator_finrank_add_eq_of_star
    (derivedEvaluationBilinearMap p hker) eChars eV hform (primeDerivedImage p N) hJ
  rwa [← derivedCharactersVanishingOn_mixedCommutator_eq_joint p hker N] at hd

theorem starDerived_mixedCommutator_not_le_radical
    (N : Subgroup G) [N.Normal]
    (hnotND : ¬N ≤ commutator G) (hnotDN : ¬commutator G ≤ N) :
    ¬⁅N, (⊤ : Subgroup G)⁆ ≤ primeRelativeRadical p (commutator G) := by
  intro hm
  have hd := starDerived_mixedVanishing_finrank_add_image p hker hG eChars eV hform N hnotDN
  have hchars : Module.finrank (ZMod p) (primeRelativeCharacters p (commutator G)) =
      Module.finrank (ZMod p) U := by
    simpa only [Subspace.dual_finrank_eq] using eChars.finrank_eq
  rw [derivedCharactersVanishingOn_eq_top_of_le_radical p _ hm, finrank_top, hchars] at hd
  have hw : Module.finrank (ZMod p) (primeDerivedImage p N) = 0 := by omega
  exact hnotND ((primeDerivedImage_eq_bot_iff_le_commutator p hker N).mp
    (Submodule.finrank_eq_zero.mp hw))

theorem starDerived_radical_le_mixed_of_comparability
    (hcompare : ∀ (M : Subgroup G) [M.Normal], M ≤ commutator G →
      M ≤ primeRelativeRadical p (commutator G) ∨ primeRelativeRadical p (commutator G) ≤ M)
    (N : Subgroup G) [N.Normal]
    (hnotND : ¬N ≤ commutator G) (hnotDN : ¬commutator G ≤ N) :
    primeRelativeRadical p (commutator G) ≤ ⁅N, (⊤ : Subgroup G)⁆ := by
  rcases hcompare ⁅N, (⊤ : Subgroup G)⁆ (Subgroup.commutator_mono le_top le_rfl) with hm | hr
  · exact False.elim
      (starDerived_mixedCommutator_not_le_radical p hker hG eChars eV hform N hnotND hnotDN hm)
  · exact hr

/-- The actual head plus the full parameter dimension is at most dim U.
The cardinal cancellation uses the same original N, B=N∩D and [N,G]. -/
theorem primeRelativeHead_add_vanishing_le_of_star_crossing
    (hcompare : ∀ (M : Subgroup G) [M.Normal], M ≤ commutator G →
      M ≤ primeRelativeRadical p (commutator G) ∨ primeRelativeRadical p (commutator G) ≤ M)
    (N : Subgroup G) [N.Normal]
    (hnotND : ¬N ≤ commutator G) (hnotDN : ¬commutator G ≤ N) :
    Module.finrank (ZMod p) (primeRelativeCharacters p N) +
        Module.finrank (ZMod p) (derivedCharactersVanishingOn p (N ⊓ commutator G)) ≤
      Module.finrank (ZMod p) U := by
  let B := N ⊓ commutator G
  let M := ⁅N, (⊤ : Subgroup G)⁆
  have hMB : M ≤ B := le_inf (Subgroup.commutator_le_left N ⊤)
    (Subgroup.commutator_mono le_top le_rfl)
  have hRM : primeRelativeRadical p (commutator G) ≤ M :=
    starDerived_radical_le_mixed_of_comparability p hker hG eChars eV hform
      hcompare N hnotND hnotDN
  have hDM : Nat.card (commutator G) =
      p ^ Module.finrank (ZMod p) (derivedCharactersVanishingOn p M) * Nat.card M :=
    primeRelativeVanishing_card_factorization p (commutator G) M
      (hMB.trans inf_le_right) hRM
  have hDB : Nat.card (commutator G) =
      p ^ Module.finrank (ZMod p) (derivedCharactersVanishingOn p B) * Nat.card B :=
    primeRelativeVanishing_card_factorization p (commutator G) B inf_le_right (hRM.trans hMB)
  have hN : p ^ Module.finrank (ZMod p) (primeDerivedImage p N) * Nat.card B = Nat.card N :=
    primeDerivedImage_pow_finrank_mul_intersection p hker N
  have hd : Module.finrank (ZMod p) (primeDerivedImage p N) +
      Module.finrank (ZMod p) (derivedCharactersVanishingOn p M) = Module.finrank (ZMod p) U :=
    starDerived_mixedVanishing_finrank_add_image p hker hG eChars eV hform N hnotDN
  have hp : p ^ (Module.finrank (ZMod p) (primeRelativeCharacters p N) +
        Module.finrank (ZMod p) (derivedCharactersVanishingOn p B)) * Nat.card B ≤
      p ^ Module.finrank (ZMod p) U * Nat.card B := by
    calc
      _ = p ^ Module.finrank (ZMod p) (primeRelativeCharacters p N) *
          (p ^ Module.finrank (ZMod p) (derivedCharactersVanishingOn p B) * Nat.card B) := by
        rw [pow_add, Nat.mul_assoc]
      _ = p ^ Module.finrank (ZMod p) (primeRelativeCharacters p N) * Nat.card (commutator G) :=
        by rw [← hDB]
      _ = p ^ Module.finrank (ZMod p) (derivedCharactersVanishingOn p M) *
          (p ^ Module.finrank (ZMod p) (primeRelativeCharacters p N) * Nat.card M) := by
        rw [hDM, Nat.mul_left_comm]
      _ ≤ p ^ Module.finrank (ZMod p) (derivedCharactersVanishingOn p M) * Nat.card N :=
        Nat.mul_le_mul_left _ (primeRelativeHead_pow_mul_mixed_card_le p N)
      _ = p ^ Module.finrank (ZMod p) U * Nat.card B := by
        rw [← hN, ← Nat.mul_assoc, ← pow_add, Nat.add_comm, hd]
  exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp
    (Nat.le_of_mul_le_mul_right hp (Nat.card_pos (α := B)))

/-- Exact common-radical dimension for the full actual vanishing space. -/
theorem starDerived_vanishing_common_finrank_add
    (N : Subgroup G) [N.Normal] (hnotDN : ¬commutator G ≤ N) :
    Module.finrank (ZMod p) (derivedCharactersVanishingOn p (N ⊓ commutator G)) +
        Module.finrank (ZMod p) (derivedVanishingCommonRadical p hker (N ⊓ commutator G)) =
      Module.finrank (ZMod p) U :=
  linearFamilyCommonRadical_finrank_add_parameter_eq_of_star
    (derivedEvaluationBilinearMap p hker) eChars eV hform
    (derivedCharactersVanishingOn p (N ⊓ commutator G))
    (derivedCharactersVanishingOn_ne_bot_of_lt p hG _
      (derivedIntersection_lt_of_not_derived_le N hnotDN))

/-- The center order keeps the same original N and complete parameter
space. It is p^(dim U-w), independently of the parameter dimension. -/
theorem quotientCenter_card_eq_pow_of_star_crossing
    (N : Subgroup G) [N.Normal] (hnotDN : ¬commutator G ≤ N)
    (hRB : primeRelativeRadical p (commutator G) ≤ N ⊓ commutator G) :
    Nat.card (Subgroup.center (G ⧸ N)) =
      p ^ (Module.finrank (ZMod p) U - Module.finrank (ZMod p) (primeDerivedImage p N)) := by
  let B := N ⊓ commutator G
  have hDB : Nat.card (commutator G) =
      p ^ Module.finrank (ZMod p) (derivedCharactersVanishingOn p B) * Nat.card B :=
    primeRelativeVanishing_card_factorization p (commutator G) B inf_le_right hRB
  have hN : p ^ Module.finrank (ZMod p) (primeDerivedImage p N) * Nat.card B = Nat.card N :=
    primeDerivedImage_pow_finrank_mul_intersection p hker N
  have hd := starDerived_vanishing_common_finrank_add p hker hG eChars eV hform N hnotDN
  have hz := quotientCenter_card_mul_inf_commutator N
  rw [quotientCenterPreimage_vanishing_card p hker B inf_le_right hRB,
    hDB, ← Nat.mul_assoc, ← pow_add, Nat.add_comm, hd, ← hN, ← Nat.mul_assoc] at hz
  have hz' : Nat.card (Subgroup.center (G ⧸ N)) *
      p ^ Module.finrank (ZMod p) (primeDerivedImage p N) = p ^ Module.finrank (ZMod p) U :=
    Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := B)) hz
  have hw : Module.finrank (ZMod p) (primeDerivedImage p N) ≤ Module.finrank (ZMod p) U := by
    have h := starDerived_mixedVanishing_finrank_add_image p hker hG eChars eV hform N hnotDN
    omega
  apply Nat.eq_of_mul_eq_mul_right
    (pow_pos (Fact.out : p.Prime).pos (Module.finrank (ZMod p) (primeDerivedImage p N)))
  rw [hz', ← pow_add, Nat.sub_add_cancel hw]

end SymmetricSubgroupAsymptotics
