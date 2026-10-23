import SymmetricSubgroupAsymptotics.PrimitiveSocleRawONanScott
import SymmetricSubgroupAsymptotics.Non2PreE7SmallModelNumerics
import SymmetricSubgroupAsymptotics.LogSquareOrderSubgroupClassBound
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! The actual second O'Nan--Scott degree form has a logarithmic-square
order bound. The original full socle and original quotient embedding are
counted; a generic generating-set automorphism bound suffices, without
CFSG, a simple-index bound, or a primitive order-classification premise.
Only the actual proper-index degree form remains in the final disjunction.
-/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure

private theorem twice_le_two_pow (a : ℕ) : 2*a ≤ 2^a := by
  cases a with
  | zero => norm_num
  | succ b =>
    have h := Nat.mul_le_mul_left 2 (Nat.succ_le_of_lt b.lt_two_pow_self)
    simpa only [pow_succ, Nat.mul_comm] using h

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.card_le_degree_pow_log_of_power_form
    (D : NonaffineData G X) (a : ℕ) (hka : D.factorCount ≤ 2*a)
    (hdegree : Nat.card X=(Nat.card D.Simple)^a) (hn : 2 ≤ Nat.card X) :
    Nat.card G ≤ (Nat.card X)^(4*Nat.log 2 (Nat.card X)+2) := by
  let s := Nat.card D.Simple
  let n := Nat.card X
  let k := D.factorCount
  let r := Nat.log 2 n
  have hs : 2 ≤ s := Finite.one_lt_card
  have hdeg : n=s^a := hdegree
  have ha : 1 ≤ a := by
    by_contra h
    have ha0 : a=0 := by omega
    rw [ha0, pow_zero] at hdeg
    omega
  have hsn : s ≤ n := by
    calc
      s = s^1 := (pow_one _).symm
      _ ≤ s^a := Nat.pow_le_pow_right (by omega) ha
      _ = n := hdeg.symm
  have hpow : 2^a ≤ n := (Nat.pow_le_pow_left hs a).trans_eq hdeg.symm
  have har : a ≤ r := Nat.le_log_of_pow_le (by decide) hpow
  have hkn : k ≤ n := hka.trans ((twice_le_two_pow a).trans hpow)
  have hkr : k ≤ 2*r := by omega
  have hlog : Nat.log 2 s ≤ r := Nat.log_mono_right hsn
  have hsocle : Nat.card (finiteGroupSocle G)=s^k := by
    rw [Nat.card_congr D.socleEquiv.toEquiv, Nat.card_fun, Nat.card_fin]
  have hsocleUpper : Nat.card (finiteGroupSocle G) ≤ n^2 := by
    rw [hsocle]
    calc
      s^k ≤ s^(2*a) := Nat.pow_le_pow_right (by omega) hka
      _ = (s^a)^2 := by rw [← pow_mul]; congr 1; omega
      _ = n^2 := congrArg (fun t : ℕ => t^2) hdeg.symm
  have houter : Nat.card (Outer D.Simple) ≤ s^r := by
    let π : MulAut D.Simple →* Outer D.Simple := QuotientGroup.mk' (Inner D.Simple)
    have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
    calc
      Nat.card (Outer D.Simple) ≤ Nat.card (MulAut D.Simple) :=
        Nat.card_le_card_of_surjective π hπ
      _ ≤ s^Nat.log 2 s :=
        Non2UnipotentPrefixFiniteMenu.mulEquiv_card_le_card_pow_log D.Simple
      _ ≤ s^r := Nat.pow_le_pow_right (by omega) hlog
  have hquotient : Nat.card (G⧸finiteGroupSocle G) ≤
      (Nat.card (Outer D.Simple))^k*k.factorial := by
    have h := Nat.card_le_card_of_injective D.quotientEmbedding D.quotientEmbedding_injective
    have he : Nat.card (OuterWreathPermutationCompression.Wreath (Outer D.Simple) k) =
        (Nat.card (Outer D.Simple))^k*k.factorial := by
      rw [PermutationalWreathProduct.natCard_eq, Nat.card_fin, Nat.card_perm, Nat.card_fin]
    exact h.trans_eq he
  have houterPower : (Nat.card (Outer D.Simple))^k ≤ n^(2*r) := by
    calc
      (Nat.card (Outer D.Simple))^k ≤ (s^r)^k := Nat.pow_le_pow_left houter k
      _ ≤ (s^r)^(2*a) := Nat.pow_le_pow_right (pow_pos (by omega) _) hka
      _ = (s^a)^(2*r) := by rw [← pow_mul, ← pow_mul]; congr 1; ring
      _ = n^(2*r) := congrArg (fun t : ℕ => t^(2*r)) hdeg.symm
  have hfactorial : k.factorial ≤ n^(2*r) :=
    (Nat.factorial_le_pow k).trans ((Nat.pow_le_pow_left hkn k).trans
      (Nat.pow_le_pow_right (by omega) hkr))
  have hquotientUpper : Nat.card (G⧸finiteGroupSocle G) ≤ n^(4*r) := by
    apply hquotient.trans
    calc
      (Nat.card (Outer D.Simple))^k*k.factorial ≤ n^(2*r)*n^(2*r) :=
        Nat.mul_le_mul houterPower hfactorial
      _ = n^(4*r) := by rw [← pow_add]; congr 1; omega
  calc
    Nat.card G = Nat.card (G⧸finiteGroupSocle G)*Nat.card (finiteGroupSocle G) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (finiteGroupSocle G)
    _ ≤ n^(4*r)*n^2 := Nat.mul_le_mul hquotientUpper hsocleUpper
    _ = n^(4*r+2) := (pow_add _ _ _).symm

theorem NonaffineData.subgroup_class_cube_le_of_power_form
    (D : NonaffineData G X) (a : ℕ) (hka : D.factorCount ≤ 2*a)
    (hdegree : Nat.card X=(Nat.card D.Simple)^a) (hn : 1024 ≤ Nat.card X)
    (H : Subgroup G) : Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) :=
  LogSquareOrderSubgroupClassBound.subgroup_class_cube_le _ hn
    (D.card_le_degree_pow_log_of_power_form a hka hdegree (by omega)) H

theorem NonaffineData.subgroup_class_cube_or_index_form
    (D : NonaffineData G X) (hn : 1024 ≤ Nat.card X) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) ∨
      ∃ K : Subgroup D.Simple, K ≠ ⊤ ∧ Nat.card X=K.index^D.factorCount := by
  rcases D.indexForm with hindex | ⟨a, hka, hdegree⟩
  · exact Or.inr hindex
  · exact Or.inl (D.subgroup_class_cube_le_of_power_form a hka hdegree hn H)

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
