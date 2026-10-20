import SymmetricSubgroupAsymptotics.ProductProjectedEpimorphismCount
import SymmetricSubgroupAsymptotics.MarkedC4RDTNormalFInterface
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Uniform bounded-target constants for the original normal-target
epimorphism theorem. Every normal target subgroup remains available; the
constant depends only on the common factor-order bound. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.ProductProjectedEpimorphismUniform
open MarkedC4

def uniformConstant (k : ℕ) : ℕ :=
  let M := 2 ^ k
  2 ^ k * M ^ k * M ^ ((M ^ k * M) ^ M)

theorem uniformConstant_pos (k : ℕ) : 0 < uniformConstant k := by
  dsimp [uniformConstant]
  positivity

private theorem genRank_pos_of_surjective {G Q : Type} [Group G] [Group Q]
    [Finite G] [Nontrivial Q] (f : G →* Q) (hf : Function.Surjective f) :
    0 < genRank G := by
  by_contra hn
  have hz : genRank G = 0 := by omega
  obtain ⟨S, hS, hgen⟩ := genRank_spec (G := G)
  have hS0 : S = ∅ := Finset.card_eq_zero.mp (hS.trans hz)
  have ht : (⊥ : Subgroup G) = ⊤ := by simpa only [hS0,
    Finset.coe_empty, Subgroup.closure_empty] using hgen
  obtain ⟨x, hx⟩ := exists_ne (1 : Q)
  obtain ⟨y, rfl⟩ := hf x
  have hy : y = 1 := by
    have hm : y ∈ (⊥ : Subgroup G) := by rw [ht]; trivial
    exact hm
  exact hx (by rw [hy, map_one])

theorem epimorphism_card_le {G Q I : Type} [Group G] [Group Q]
    [Finite G] [Finite Q] [Nontrivial Q] [Fintype I]
    (P : I → Type) [∀ i, Group (P i)] [∀ i, Finite (P i)]
    (π : G →* ∀ i, P i) (hG : IsPGroup 2 G) (hQ : IsPGroup 2 Q)
    (hπ : Function.Surjective π) (F : Subgroup Q) [F.Normal]
    (k dN : ℕ) (hQcard : Nat.card Q ≤ 2 ^ k)
    (hPcard : ∀ i, Nat.card (P i) ≤ 2 ^ k)
    (hd : ∀ U : Subgroup G, U.Normal →
      U ≤ commutator G ⊓ π.ker → normalGen U ≤ dN) :
    Nat.card {f : G →* Q // Function.Surjective f} ≤
      uniformConstant k * genRank G ^ k *
        Nat.card (Subgroup.centralizer (F : Set Q)) ^ genRank G *
        Nat.card (⁅F, (⊤ : Subgroup Q)⁆ : Subgroup Q) ^ dN := by
  let E := {f : G →* Q // Function.Surjective f}
  by_cases hE : Nonempty E
  · obtain ⟨f⟩ := hE
    have hdpos := genRank_pos_of_surjective f.1 f.2
    let q := Nat.log 2 (Nat.card Q)
    let M := 2 ^ k
    let c := Nat.card (⁅F, (⊤ : Subgroup Q)⁆ : Subgroup Q)
    have hMpos : 0 < M := by dsimp [M]; positivity
    have hMone : 1 ≤ M := hMpos
    have hq : q ≤ k := by
      have h := Nat.log_mono_right (b := 2) hQcard
      simpa only [Nat.log_pow (by decide : 1 < 2)] using h
    have hc : c ≤ M := (Subgroup.card_le_card_group _).trans hQcard
    have hF : Nat.card F ≤ M := (Subgroup.card_le_card_group F).trans hQcard
    have hpoly : (genRank G + 1) ^ q ≤ 2 ^ k * genRank G ^ k := by
      calc
        (genRank G + 1) ^ q ≤ (genRank G + 1) ^ k :=
          Nat.pow_le_pow_right (by omega) hq
        _ ≤ (2 * genRank G) ^ k := Nat.pow_le_pow_left (by omega) _
        _ = _ := Nat.mul_pow _ _ _
    have htarget : Nat.card Q ^ q ≤ M ^ k :=
      (Nat.pow_le_pow_left hQcard _).trans (Nat.pow_le_pow_right hMpos hq)
    have hinner : M ^ q * c ≤ M ^ k * M :=
      Nat.mul_le_mul (Nat.pow_le_pow_right hMpos hq) hc
    have hinnerpos : 0 < M ^ k * M := by positivity
    have hexponent : (M ^ q * c) ^ Nat.card F ≤ (M ^ k * M) ^ M :=
      (Nat.pow_le_pow_left hinner _).trans
        (Nat.pow_le_pow_right hinnerpos hF)
    have hconstant : Nat.card Q ^ ((M ^ q * c) ^ Nat.card F) ≤
        M ^ ((M ^ k * M) ^ M) :=
      (Nat.pow_le_pow_left hQcard _).trans
        (Nat.pow_le_pow_right hMpos hexponent)
    have h := ProductProjectedEpimorphismCount.epimorphism_card_le P π 2
      hG hQ hπ F M dN hMpos hPcard hd
    calc
      Nat.card E ≤ (genRank G + 1) ^ q * Nat.card Q ^ q * c ^ dN *
          (Nat.card Q ^ ((M ^ q * c) ^ Nat.card F) *
            Nat.card (Subgroup.centralizer (F : Set Q)) ^ genRank G) := h
      _ ≤ (2 ^ k * genRank G ^ k) * (M ^ k) * c ^ dN *
          (M ^ ((M ^ k * M) ^ M) *
            Nat.card (Subgroup.centralizer (F : Set Q)) ^ genRank G) :=
        Nat.mul_le_mul
          (Nat.mul_le_mul_right _ (Nat.mul_le_mul hpoly htarget))
          (Nat.mul_le_mul_right _ hconstant)
      _ = _ := by dsimp [uniformConstant, M, c]; ac_rfl
  · letI : IsEmpty E := not_nonempty_iff.mp hE
    exact (Nat.card_of_isEmpty (α := E)).le.trans (Nat.zero_le _)

end SymmetricSubgroupAsymptotics.ProductProjectedEpimorphismUniform
