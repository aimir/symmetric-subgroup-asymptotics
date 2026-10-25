import SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupDegree
import Mathlib.GroupTheory.GroupAction.Period
import Mathlib.Data.Finite.Perm
import Mathlib.Data.Nat.Prime.Factorial

/-! A selected vector of prime period survives a literal quotient whose
kernel lies in a subgroup of order prime to that prime. The resulting
simple-group coset bound uses the actual quotient and action. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimePeriodSimpleQuotientIndex

variable {G Q X : Type*} [Group G] [Finite G] [Group Q] [Finite Q]

theorem prime_dvd_card_of_point_period [MulAction G X]
    (p : ℕ) (hp : p.Prime) (g : G) (x : X)
    (hperiod : g^p • x = x) (hmoved : g • x ≠ x) : p ∣ Nat.card G := by
  have hd : MulAction.period g x ∣ p :=
    (MulAction.pow_smul_eq_iff_period_dvd).mp hperiod
  have hne : MulAction.period g x ≠ 1 := by
    intro h
    exact hmoved (MulAction.period_eq_one_iff.mp h)
  have he : MulAction.period g x = p := (Nat.dvd_prime hp).mp hd |>.resolve_left hne
  rw [←he]
  exact (MulAction.period_dvd_orderOf g x).trans (orderOf_dvd_natCard g)

theorem prime_dvd_card_quotient_of_kernel_le
    (p : ℕ) (hp : p.Prime) (f : G →* Q) (hf : Function.Surjective f)
    (B : Subgroup G) (hker : f.ker ≤ B) (hB : ¬p ∣ Nat.card B)
    (hG : p ∣ Nat.card G) : p ∣ Nat.card Q := by
  have hnker : ¬p ∣ Nat.card f.ker := fun h =>
    hB (h.trans (Subgroup.card_dvd_of_le hker))
  have hcard : Nat.card G = Nat.card Q * Nat.card f.ker := by
    calc
      _ = Nat.card (G ⧸ f.ker) * Nat.card f.ker :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
      _ = _ := congrArg (fun n : ℕ => n * Nat.card f.ker)
        (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv)
  rw [hcard] at hG
  exact (hp.dvd_mul.mp hG).resolve_right hnker

theorem prime_le_proper_index [IsSimpleGroup Q]
    (p : ℕ) (hp : p.Prime) (hQ : p ∣ Nat.card Q)
    (H : Subgroup Q) (hH : H ≠ ⊤) : p ≤ H.index := by
  let f := MulAction.toPermHom Q (Q ⧸ H)
  have hinj : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro g hg
    apply Subgroup.mem_bot.mpr
    by_contra hne
    obtain ⟨x,hx⟩ := CFSGConjugateSubgroupDegree.exists_moved_coset_of_ne_one H hH g hne
    exact hx (congrArg (fun a : Equiv.Perm (Q ⧸ H) => a x) (MonoidHom.mem_ker.mp hg))
  have hd : p ∣ Nat.card (Equiv.Perm (Q ⧸ H)) :=
    hQ.trans (Subgroup.card_dvd_of_injective f hinj)
  rw [Nat.card_perm, ←H.index_eq_card] at hd
  exact hp.dvd_factorial.mp hd

theorem prime_le_proper_index_of_point_period [MulAction G X] [IsSimpleGroup Q]
    (p : ℕ) (hp : p.Prime) (f : G →* Q) (hf : Function.Surjective f)
    (B : Subgroup G) (hker : f.ker ≤ B) (hB : ¬p ∣ Nat.card B)
    (g : G) (x : X) (hperiod : g^p • x = x) (hmoved : g • x ≠ x)
    (H : Subgroup Q) (hH : H ≠ ⊤) : p ≤ H.index :=
  prime_le_proper_index p hp
    (prime_dvd_card_quotient_of_kernel_le p hp f hf B hker hB
      (prime_dvd_card_of_point_period p hp g x hperiod hmoved)) H hH

end SymmetricSubgroupAsymptotics.PrimePeriodSimpleQuotientIndex
