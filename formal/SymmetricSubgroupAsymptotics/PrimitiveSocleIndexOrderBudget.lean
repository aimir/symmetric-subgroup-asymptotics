import SymmetricSubgroupAsymptotics.PrimitiveSoclePowerDegreeOrderBound
import SymmetricSubgroupAsymptotics.WideLogSquareOrderClassNumerics

/-! One original-model order budget covers every factor count in the
proper-index degree form. The input concerns the literal simple group
and its outer automorphisms; the actual full socle and quotient embedding
then give the ambient order and class bounds. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure

theorem power_factorial_log_order_le (m k : ℕ) (hm : 2 ≤ m) (hk : 1 ≤ k) :
    (m^(4*Nat.log 2 m+23))^k*k.factorial ≤
      (m^k)^(4*Nat.log 2 (m^k)+24) := by
  let l := Nat.log 2 m
  let L := Nat.log 2 (m^k)
  have hl : 1 ≤ l := Nat.le_log_of_pow_le (by decide) (by simpa using hm)
  have hmpos : 0 < m := by omega
  have hnpos : 0 < m^k := pow_pos hmpos _
  have hkn : k ≤ m^k := k.lt_two_pow_self.le.trans (Nat.pow_le_pow_left hm k)
  have hlog : k*l ≤ L := by
    apply Nat.le_log_of_pow_le (by decide)
    calc
      2^(k*l) = (2^l)^k := by rw [←pow_mul]; congr 1; ring
      _ ≤ m^k := Nat.pow_le_pow_left (Nat.pow_log_le_self 2 (by omega)) k
  have hexp : 4*l+k ≤ 4*(k*l)+1 := by
    induction k, hk using Nat.le_induction with
    | base => omega
    | succ k hk ih => nlinarith
  have hsum : 4*l+23+k ≤ 4*L+24 := by omega
  calc
    (m^(4*Nat.log 2 m+23))^k*k.factorial ≤
        (m^(4*l+23))^k*(m^k)^k :=
      Nat.mul_le_mul_left _ ((Nat.factorial_le_pow k).trans (Nat.pow_le_pow_left hkn k))
    _ = (m^k)^(4*l+23+k) := by
      have he : (m^(4*l+23))^k = (m^k)^(4*l+23) := by
        rw [←pow_mul, ←pow_mul, Nat.mul_comm]
      rw [he]
      exact (pow_add (m^k) (4*l+23) k).symm
    _ ≤ (m^k)^(4*L+24) := Nat.pow_le_pow_right hnpos hsum

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.card_le_log_order_of_index_form
    (D : NonaffineData G X) (K : Subgroup D.Simple) (hK : K ≠ ⊤)
    (hdegree : Nat.card X=K.index^D.factorCount)
    (hautomorphism : Nat.card D.Simple*Nat.card (Outer D.Simple) ≤
      K.index^(4*Nat.log 2 K.index+23)) :
    Nat.card G ≤ (Nat.card X)^(4*Nat.log 2 (Nat.card X)+24) := by
  let s := Nat.card D.Simple
  let o := Nat.card (Outer D.Simple)
  let k := D.factorCount
  have hsocle : Nat.card (finiteGroupSocle G)=s^k := by
    rw [Nat.card_congr D.socleEquiv.toEquiv, Nat.card_fun, Nat.card_fin]
  have hquotient : Nat.card (G⧸finiteGroupSocle G) ≤ o^k*k.factorial := by
    have h := Nat.card_le_card_of_injective D.quotientEmbedding D.quotientEmbedding_injective
    have he : Nat.card (OuterWreathPermutationCompression.Wreath (Outer D.Simple) k)=
        o^k*k.factorial := by
      rw [PermutationalWreathProduct.natCard_eq, Nat.card_fin, Nat.card_perm, Nat.card_fin]
    exact h.trans_eq he
  calc
    Nat.card G = Nat.card (G⧸finiteGroupSocle G)*Nat.card (finiteGroupSocle G) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (finiteGroupSocle G)
    _ ≤ (o^k*k.factorial)*s^k := Nat.mul_le_mul hquotient hsocle.le
    _ = (s*o)^k*k.factorial := by rw [mul_pow]; ring
    _ ≤ (K.index^(4*Nat.log 2 K.index+23))^k*k.factorial :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hautomorphism k)
    _ ≤ (K.index^k)^(4*Nat.log 2 (K.index^k)+24) :=
      power_factorial_log_order_le K.index k (K.one_lt_index_of_ne_top hK) D.factorCount_pos
    _ = (Nat.card X)^(4*Nat.log 2 (Nat.card X)+24) := by rw [hdegree]

theorem NonaffineData.subgroup_class_cube_le_of_index_order_budget
    (D : NonaffineData G X) (K : Subgroup D.Simple) (hK : K ≠ ⊤)
    (hdegree : Nat.card X=K.index^D.factorCount)
    (hautomorphism : Nat.card D.Simple*Nat.card (Outer D.Simple) ≤
      K.index^(4*Nat.log 2 K.index+23)) (hn : 1024 ≤ Nat.card X)
    (H : Subgroup G) : Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) :=
  WideLogSquareOrderClassNumerics.subgroup_class_cube_le _ hn
    (D.card_le_log_order_of_index_form K hK hdegree hautomorphism) H

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
