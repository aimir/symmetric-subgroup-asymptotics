import SymmetricSubgroupAsymptotics.AbelianProductGraphClassification
import SymmetricSubgroupAsymptotics.PrimeElementaryEpimorphismBound
import SymmetricSubgroupAsymptotics.TernarySubspaceEnvelope

/-!
# Ternary product graphs over a permutation tail

This is the algebraic counting lemma used by the finite width-three packet.
It classifies every subgroup of an elementary ternary group times an
arbitrary finite group, retains the literal second-coordinate image, and
bounds the graph character by that image's ternary character rank.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace TernaryProductGraphBound

abbrev Space (c : ℕ) := Fin c → ZMod 3
abbrev Elementary (c : ℕ) := Multiplicative (Space c)

def subgroupOrderIso (c : ℕ) :
    Submodule (ZMod 3) (Space c) ≃o Subgroup (Elementary c) :=
  (AddSubgroup.toZModSubmodule 3).symm.trans AddSubgroup.toSubgroup

private theorem quotientMap_ker (c : ℕ)
    (S : Submodule (ZMod 3) (Space c)) :
    (S.mkQ.toAddMonoidHom.toMultiplicative).ker =
      S.toAddSubgroup.toSubgroup := by
  ext v
  change S.mkQ v.toAdd = 0 ↔ v.toAdd ∈ S
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

private def quotientEquiv (c : ℕ) (K : Subgroup (Elementary c)) :
    Elementary c ⧸ K ≃* Multiplicative (Space c ⧸ (subgroupOrderIso c).symm K) := by
  let S := (subgroupOrderIso c).symm K
  let q : Elementary c →* Multiplicative (Space c ⧸ S) :=
    S.mkQ.toAddMonoidHom.toMultiplicative
  have hK : K = S.toAddSubgroup.toSubgroup := by
    change K = subgroupOrderIso c S
    exact ((subgroupOrderIso c).apply_symm_apply K).symm
  exact (QuotientGroup.quotientMulEquivOfEq hK).trans
    ((QuotientGroup.quotientMulEquivOfEq (quotientMap_ker c S).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q (by
        intro x
        obtain ⟨v, rfl⟩ := S.mkQ_surjective x.toAdd
        exact ⟨Multiplicative.ofAdd v, rfl⟩)))

theorem quotient_hom_card_le (c d : ℕ) {B : Type*} [Group B] [Finite B]
    (K : Subgroup (Elementary c))
    (hd : Module.finrank (ZMod 3) (PrimeCharacters 3 B) ≤ d) :
    Nat.card (B →* Elementary c ⧸ K) ≤ 3 ^ (d * c) := by
  let S := (subgroupOrderIso c).symm K
  let e := quotientEquiv c K
  have hcard : Nat.card (B →* Elementary c ⧸ K) =
      3 ^ (Module.finrank (ZMod 3) (PrimeCharacters 3 B) *
        Module.finrank (ZMod 3) (Space c ⧸ S)) := by
    rw [Nat.card_congr e.monoidHomCongrRightEquiv]
    exact primeAbelianizationGroupHom_card 3 B
  rw [hcard]
  apply Nat.pow_le_pow_right (by decide : 0 < 3)
  apply Nat.mul_le_mul hd
  simpa only [Module.finrank_pi, Fintype.card_fin] using S.finrank_quotient_le

private abbrev RankSubspace (c r : ℕ) :=
  {S : Submodule (ZMod 3) (Space c) // Module.finrank (ZMod 3) S = r}

private def rankIndex (c : ℕ) (S : Submodule (ZMod 3) (Space c)) : Fin (c + 1) :=
  ⟨Module.finrank (ZMod 3) S, Nat.lt_succ_of_le (by simpa using S.finrank_le)⟩

private theorem submodule_card_eq_rank_sum (c : ℕ) :
    Nat.card (Submodule (ZMod 3) (Space c)) =
      ∑ r : Fin (c + 1), Nat.card (RankSubspace c r) := by
  let e := Equiv.sigmaFiberEquiv (rankIndex c)
  rw [← Nat.card_congr e, Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro r _
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (fun _ => Fin.ext_iff)

theorem submodule_card_le (c : ℕ) :
    Nat.card (Submodule (ZMod 3) (Space c)) ≤
      (c + 1) * 3 ^ (c * c / 4 + c) := by
  rw [submodule_card_eq_rank_sum]
  calc
    _ ≤ ∑ _r : Fin (c + 1), 3 ^ (c * c / 4 + c) := by
      apply Finset.sum_le_sum
      intro r _
      have hr := TernarySubspaceEnvelope.rank_count_le c r (by omega)
      apply hr.trans
      apply Nat.pow_le_pow_right (by decide : 0 < 3)
      have hrc : r.val ≤ c := by omega
      have hsq : 4 * (r.val * (c - r.val)) ≤ c * c := by
        have hsq' : 4 * (r.val : ℤ) * ((c : ℤ) - r.val) ≤
            (c : ℤ) * c := by
          nlinarith [sq_nonneg ((c : ℤ) - 2 * r.val)]
        have hsq'' : 4 * r.val * (c - r.val) ≤ c * c := by
          exact_mod_cast hsq'
        simpa only [mul_assoc] using hsq''
      have hs : (r.val * (c - r.val + 1)) * 4 ≤ c * c + c * 4 := by
        rw [Nat.mul_add, Nat.mul_one]
        nlinarith
      have hdiv : r.val * (c - r.val + 1) ≤ (c * c + c * 4) / 4 :=
        (Nat.le_div_iff_mul_le (by norm_num)).2 hs
      calc
        r.val * (c - r.val + 1) ≤ (c * c + c * 4) / 4 := hdiv
        _ = c * c / 4 + c := by
          rw [Nat.add_mul_div_right]
          norm_num
    _ = _ := by simp [Finset.sum_const]

/-- The literal second image selected by the exact product classification. -/
def TailRankCapped (c d : ℕ) {B : Type*} [Group B]
    (H : Subgroup (Elementary c × B)) : Prop :=
  Module.finrank (ZMod 3)
    (PrimeCharacters 3 ((AbelianProductGraphClassification.classification H).1)) ≤ d

theorem tail_of_classification (c : ℕ) {B : Type*} [Group B]
    (H : Subgroup (Elementary c × B)) :
    (AbelianProductGraphClassification.classification H).1 =
      H.map (MonoidHom.snd (Elementary c) B) := rfl

private instance subgroupFinite {G : Type*} [Group G] [Finite G] :
    Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective

private instance homFinite {G Q : Type*} [Group G] [Group Q] [Finite G] [Finite Q] :
    Finite (G →* Q) :=
  Finite.of_injective (fun f : G →* Q => (f : G → Q)) DFunLike.coe_injective

private instance quotientFinite (c : ℕ) (K : Subgroup (Elementary c)) :
    Finite (Elementary c ⧸ K) :=
  Finite.of_surjective (QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K)

attribute [local instance] Fintype.ofFinite

/-- Uniform count of all product graphs when every actual tail image has the
stated ternary character-rank bound.  Keeping the actual image is essential:
the hypothesis is applied to that subgroup rather than to the ambient tail.
The physical packet supplies the decisive Gaussian loss. -/
theorem card_le_of_all_tail_rank_le (c d : ℕ)
    {B : Type*} [Group B] [Finite B]
    (hd : ∀ L : Subgroup B,
      Module.finrank (ZMod 3) (PrimeCharacters 3 L) ≤ d) :
    Nat.card (Subgroup (Elementary c × B)) ≤
      Nat.card (Subgroup B) *
        ((c + 1) * 3 ^ (c * c / 4 + c + d * c)) := by
  calc
    Nat.card (Subgroup (Elementary c × B)) =
        ∑ L : Subgroup B, ∑ K : Subgroup (Elementary c),
          Nat.card (L →* Elementary c ⧸ K) :=
      AbelianProductGraphClassification.card_eq_sum_hom
    _ ≤ ∑ _L : Subgroup B,
          ((c + 1) * 3 ^ (c * c / 4 + c + d * c)) := by
        apply Finset.sum_le_sum
        intro L _
        calc
          (∑ K : Subgroup (Elementary c), Nat.card (L →* Elementary c ⧸ K))
              ≤ ∑ _K : Subgroup (Elementary c), 3 ^ (d * c) := by
                exact Finset.sum_le_sum (fun K _ => quotient_hom_card_le c d K (hd L))
          _ = Nat.card (Subgroup (Elementary c)) * 3 ^ (d * c) := by
                simp [Nat.card_eq_fintype_card]
          _ = Nat.card (Submodule (ZMod 3) (Space c)) * 3 ^ (d * c) := by
                rw [Nat.card_congr (subgroupOrderIso c).toEquiv]
          _ ≤ ((c + 1) * 3 ^ (c * c / 4 + c)) * 3 ^ (d * c) :=
                Nat.mul_le_mul_right _ (submodule_card_le c)
          _ = (c + 1) * 3 ^ (c * c / 4 + c + d * c) := by
                rw [pow_add]
                ring
    _ = Nat.card (Subgroup B) *
          ((c + 1) * 3 ^ (c * c / 4 + c + d * c)) := by
        simp [Nat.card_eq_fintype_card]

/-- The same graph count restricted to subgroups whose *actual* second
image satisfies a predicate.  This is the form needed after the non-small
tail has been merged into one symmetric-group block: no assertion is made
about subgroups outside the retained predicate. -/
theorem card_tailRankCapped_le (c d : ℕ)
    {B : Type*} [Group B] [Finite B] :
    Nat.card {H : Subgroup (Elementary c × B) // TailRankCapped c d H} ≤
      Nat.card (Subgroup B) *
        ((c + 1) * 3 ^ (c * c / 4 + c + d * c)) := by
  let GoodTail := {L : Subgroup B //
    Module.finrank (ZMod 3) (PrimeCharacters 3 L) ≤ d}
  let Target := Σ L : GoodTail,
    Σ K : Subgroup (Elementary c), L.1 →* Elementary c ⧸ K
  let f : {H : Subgroup (Elementary c × B) // TailRankCapped c d H} → Target :=
    fun H =>
      let z := AbelianProductGraphClassification.classification H.1
      ⟨⟨z.1, H.2⟩, z.2⟩
  have hf : Function.Injective f := by
    intro H K h
    apply Subtype.ext
    apply (AbelianProductGraphClassification.classification
      (E := Elementary c) (B := B)).injective
    exact congrArg (fun z : Target => (⟨z.1.1, z.2⟩ :
      Σ L : Subgroup B, Σ K : Subgroup (Elementary c),
        L →* Elementary c ⧸ K)) h
  have hcard : Nat.card {H : Subgroup (Elementary c × B) // TailRankCapped c d H} ≤
      Nat.card Target := Nat.card_le_card_of_injective f hf
  apply hcard.trans
  calc
    Nat.card Target = ∑ L : GoodTail,
        ∑ K : Subgroup (Elementary c), Nat.card (L.1 →* Elementary c ⧸ K) := by
      simp only [Target, Nat.card_sigma]
    _ ≤ ∑ _L : GoodTail,
          ((c + 1) * 3 ^ (c * c / 4 + c + d * c)) := by
      apply Finset.sum_le_sum
      intro L _
      calc
        (∑ K : Subgroup (Elementary c), Nat.card (L.1 →* Elementary c ⧸ K))
            ≤ ∑ _K : Subgroup (Elementary c), 3 ^ (d * c) := by
              exact Finset.sum_le_sum (fun K _ => quotient_hom_card_le c d K L.2)
        _ = Nat.card (Subgroup (Elementary c)) * 3 ^ (d * c) := by
              simp [Nat.card_eq_fintype_card]
        _ = Nat.card (Submodule (ZMod 3) (Space c)) * 3 ^ (d * c) := by
              rw [Nat.card_congr (subgroupOrderIso c).toEquiv]
        _ ≤ ((c + 1) * 3 ^ (c * c / 4 + c)) * 3 ^ (d * c) :=
              Nat.mul_le_mul_right _ (submodule_card_le c)
        _ = (c + 1) * 3 ^ (c * c / 4 + c + d * c) := by
              rw [pow_add]
              ring
    _ = Nat.card GoodTail *
          ((c + 1) * 3 ^ (c * c / 4 + c + d * c)) := by
        simp [Nat.card_eq_fintype_card]
    _ ≤ Nat.card (Subgroup B) *
          ((c + 1) * 3 ^ (c * c / 4 + c + d * c)) := by
      apply Nat.mul_le_mul_right
      exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective

end TernaryProductGraphBound
end SymmetricSubgroupAsymptotics

end
