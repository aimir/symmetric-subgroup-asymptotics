import SymmetricSubgroupAsymptotics.TransitiveSixOddNormalWreath
import Mathlib.Data.Nat.Factorization.Basic

/-! Every binary quotient of an actual faithful transitive six-point
group has at most eight elements. The proof uses only orbit structure
and the two-part of 6!, without a transitive-group classification. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
local instance transitiveSixBinaryQuotientCardPrime2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {G : Type} [Group G] [Finite G]
    [MulAction G (Fin 6)] [FaithfulSMul G (Fin 6)]
    [MulAction.IsPretransitive G (Fin 6)]

/-- All denominators are actual normal subgroups of the original top. -/
theorem transitiveSix_binary_quotient_card_le_eight
    (N : Subgroup G) [N.Normal] (hQ : IsPGroup 2 (G ⧸ N)) :
    Nat.card (G ⧸ N) ≤ 8 := by
  have hG : Nat.card G ∣ 720 := by
    have h := Subgroup.card_dvd_of_injective (MulAction.toPermHom G (Fin 6))
      (show Function.Injective (MulAction.toPermHom G (Fin 6)) from by
        intro a b hab
        apply eq_of_smul_eq_smul (α := Fin 6)
        intro x
        exact congrArg (fun p : Equiv.Perm (Fin 6) => p x) hab)
    simpa only [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin] using h
  have hqdiv : Nat.card (G ⧸ N) ∣ Nat.card G := by
    rw [← Subgroup.index_eq_card]
    exact N.index_dvd_card
  obtain ⟨a,ha⟩ := hQ.exists_card_eq
  have hpow : 2^a ∣ 720 := ha ▸ hqdiv.trans hG
  have ha4 : a ≤ 4 := by
    have h := (Nat.prime_two.pow_dvd_iff_le_factorization (by decide : 720 ≠ 0)).mp hpow
    simpa only [show Nat.factorization 720 2 = 4 by decide +kernel] using h
  by_contra hlarge
  have hq16 : Nat.card (G ⧸ N) = 16 := by
    interval_cases a <;> norm_num at ha <;> omega
  have hprod : Nat.card N * 16 = Nat.card G := by
    simpa only [Subgroup.index_eq_card,hq16] using N.card_mul_index
  have hNdiv : Nat.card N ∣ 45 := by
    obtain ⟨k,hk⟩ := hG
    refine ⟨k,?_⟩
    have hk' : 720 = (Nat.card N * 16) * k :=
      hk.trans (congrArg (fun n : ℕ => n*k) hprod.symm)
    nlinarith [hk']
  have hNodd : ¬ 2 ∣ Nat.card N := by
    intro h
    have hbad : 2 ∣ 45 := h.trans hNdiv
    norm_num at hbad
  have hNne : N ≠ ⊥ := by
    intro hN
    have h16 : Nat.card G = 16 := by simpa only [hN,Subgroup.card_bot,one_mul] using hprod.symm
    have h6 : 6 ∣ Nat.card G := by
      have h := (MulAction.stabilizer G (0 : Fin 6)).index_dvd_card
      simpa only [MulAction.index_stabilizer_of_transitive,Nat.card_fin] using h
    rw [h16] at h6
    norm_num at h6
  have h72 := transitiveSix_odd_normal_card_dvd_seventyTwo N hNne hNodd
  have hbad : 16 ∣ 72 := hq16 ▸ hqdiv.trans h72
  norm_num at hbad

/-- The endpoint for any actual onto map, retaining its literal kernel. -/
theorem transitiveSix_binary_epimorphism_card_le_eight
    {B : Type} [Group B] (f : G →* B) (hf : Function.Surjective f)
    (hB : IsPGroup 2 B) : Nat.card B ≤ 8 := by
  letI : Finite B := Finite.of_surjective f hf
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  have hQ : IsPGroup 2 (G ⧸ f.ker) := hB.of_equiv e.symm
  rw [← Nat.card_congr e.toEquiv]
  exact transitiveSix_binary_quotient_card_le_eight f.ker hQ

end SymmetricSubgroupAsymptotics
end
