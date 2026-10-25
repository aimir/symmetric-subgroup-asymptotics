import SymmetricSubgroupAsymptotics.SubnormalCoordinateProperClassSaving
import SymmetricSubgroupAsymptotics.SubnormalCoordinateClassPowerBound

/-! A deficient actual coordinate product saves one proper-subnormal
POWER budget. The conditional kernels and their actual image groups are
retained, so this does not assume independent coordinates or class
monotonicity under base enlargement. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.SubnormalCoordinateProperClassPowerSaving
open SubnormalCoordinateClassBound

theorem class_power_le_of_card_lt_product (d n B P : ℕ)
    (V : Fin n → Type*) [∀ i, Group (V i)] [∀ i, Finite (V i)]
    (hbudget : ∀ i (L : Subgroup (V i)), L.IsSubnormal → Nat.card (ConjClasses L) ^ d ≤ B)
    (hproper : ∀ i (L : Subgroup (V i)), L.IsSubnormal → L ≠ ⊤ →
      Nat.card (ConjClasses L) ^ d ≤ P)
    (H : Type*) [Group H] [Finite H] (f : ∀ i, H →* V i)
    (himage : ∀ i, (f i).range.IsSubnormal)
    (hinj : Function.Injective (fun x => fun i => f i x))
    (hcard : Nat.card H < ∏ i, Nat.card (V i)) :
    Nat.card (ConjClasses H) ^ d ≤ P * B ^ (n - 1) := by
  induction n generalizing H with
  | zero =>
    have hp : 0 < Nat.card H := Nat.card_pos
    simp only [Fin.prod_univ_zero] at hcard
    omega
  | succ n ih =>
    let K : Subgroup H := (f 0).ker
    letI : K.Normal := by dsimp only [K]; infer_instance
    let tail : ∀ i : Fin n, K →* V i.succ := fun i => (f i.succ).comp K.subtype
    have htail : Function.Injective (fun x => fun i => tail i x) := by
      intro x y he
      apply Subtype.ext
      apply hinj
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact x.property.trans y.property.symm
      · exact congrFun he j
    have himageTail : ∀ i, (tail i).range.IsSubnormal := by
      intro i
      dsimp only [tail]
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
      exact map_normal_isSubnormal_of_range (f i.succ) (himage i.succ) K inferInstance
    have hsplit := Nat.pow_le_pow_left (conjugacyClass_card_le_kernel_mul_range (f 0)) d
    rw [mul_pow] at hsplit
    by_cases hr : (f 0).range = ⊤
    · have hc : Nat.card K * Nat.card (V 0) = Nat.card H := by
        have h := (f 0).ker.card_mul_index
        rw [Subgroup.index_ker] at h
        have he : Nat.card (f 0).range = Nat.card (V 0) := by
          rw [hr]
          exact Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup (V 0)) ≃* V 0).toEquiv
        simpa only [he] using h
      have hcardTail : Nat.card K < ∏ i : Fin n, Nat.card (V i.succ) := by
        rw [← hc, Fin.prod_univ_succ, Nat.mul_comm (Nat.card K) (Nat.card (V 0))] at hcard
        exact Nat.lt_of_mul_lt_mul_left hcard
      by_cases hn : n = 0
      · subst n
        have hp : 0 < Nat.card K := Nat.card_pos
        simp only [Fin.prod_univ_zero] at hcardTail
        omega
      · have hK := ih (V := fun i : Fin n => V i.succ)
          (hbudget := fun i => hbudget i.succ) (hproper := fun i => hproper i.succ)
          (H := K) (f := tail) himageTail htail hcardTail
        have hR := hbudget 0 (f 0).range (himage 0)
        have he : (P * B ^ (n - 1)) * B = P * B ^ n := by
          rw [Nat.mul_assoc, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n)]
        exact (hsplit.trans (Nat.mul_le_mul hK hR)).trans_eq
          (by simpa only [Nat.add_sub_cancel] using he)
    · have hK : Nat.card (ConjClasses K) ^ d ≤ B ^ n := by
        have h := SubnormalCoordinateClassPowerBound.class_power_le_subnormal_coordinate_bounds
          d n (fun i : Fin n => V i.succ) (fun _ => B) tail himageTail
          (fun i => hbudget i.succ) htail
        simpa only [Fin.prod_const] using h
      have hR := hproper 0 (f 0).range (himage 0) hr
      exact (hsplit.trans (Nat.mul_le_mul hK hR)).trans_eq
        (by simp only [Nat.add_sub_cancel, Nat.mul_comm])

theorem class_power_saving_or_full_product (d n B P : ℕ)
    (V : Fin n → Type*) [∀ i, Group (V i)] [∀ i, Finite (V i)]
    (hbudget : ∀ i (L : Subgroup (V i)), L.IsSubnormal → Nat.card (ConjClasses L) ^ d ≤ B)
    (hproper : ∀ i (L : Subgroup (V i)), L.IsSubnormal → L ≠ ⊤ →
      Nat.card (ConjClasses L) ^ d ≤ P)
    (H : Type*) [Group H] [Finite H] (f : ∀ i, H →* V i)
    (himage : ∀ i, (f i).range.IsSubnormal)
    (hinj : Function.Injective (fun x => fun i => f i x)) :
    Nat.card (ConjClasses H) ^ d ≤ P * B ^ (n - 1) ∨
      Function.Surjective (fun x => fun i => f i x) := by
  by_cases hcard : Nat.card H < ∏ i, Nat.card (V i)
  · exact Or.inl (class_power_le_of_card_lt_product d n B P V hbudget hproper H f himage hinj hcard)
  · right
    apply ((Nat.bijective_iff_injective_and_card (fun x => fun i => f i x)).mpr ⟨hinj, ?_⟩).surjective
    rw [Nat.card_pi]
    have hle : Nat.card H ≤ ∏ i, Nat.card (V i) := by
      simpa only [Nat.card_pi] using Nat.card_le_card_of_injective _ hinj
    exact hle.antisymm (le_of_not_gt hcard)

end SymmetricSubgroupAsymptotics.SubnormalCoordinateProperClassPowerSaving
