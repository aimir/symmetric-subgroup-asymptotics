import SymmetricSubgroupAsymptotics.MarkedC4Filtration

/-!
# Product and cyclic-four columns

The Hall splice uses the literal columns of `A × C₄^r`.  This file proves
that binary columns add under products and computes the two nonzero columns
of the cyclic-four factor.  These are structural identities, independent of
the later tableau estimates.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace MarkedC4

universe u v

/-- Squares in a direct product are the direct product of the square
subgroups. -/
def sqsProdEquiv (A : Type u) (B : Type v) [CommGroup A] [CommGroup B] :
    sqs (A × B) ≃* sqs A × sqs B where
  toFun x :=
    (⟨x.1.1, by
      obtain ⟨y, hy⟩ := x.2
      exact ⟨y.1, congrArg Prod.fst hy⟩⟩,
     ⟨x.1.2, by
      obtain ⟨y, hy⟩ := x.2
      exact ⟨y.2, congrArg Prod.snd hy⟩⟩)
  invFun x :=
    ⟨(x.1.1, x.2.1), by
      obtain ⟨a, ha⟩ := x.1.2
      obtain ⟨b, hb⟩ := x.2.2
      exact ⟨(a, b), Prod.ext ha hb⟩⟩
  left_inv x := by ext <;> rfl
  right_inv x := by ext <;> rfl
  map_mul' x y := by ext <;> rfl

/-- The two-torsion in a direct product is the product of the two-torsion
subgroups. -/
def tors2ProdEquiv (A : Type u) (B : Type v) [CommGroup A] [CommGroup B] :
    tors2 (A × B) ≃ tors2 A × tors2 B where
  toFun x :=
    (⟨x.1.1, by
      rw [mem_tors2]
      exact congrArg Prod.fst ((mem_tors2 x.1).mp x.2)⟩,
     ⟨x.1.2, by
      rw [mem_tors2]
      exact congrArg Prod.snd ((mem_tors2 x.1).mp x.2)⟩)
  invFun x :=
    ⟨(x.1.1, x.2.1), by
      rw [mem_tors2]
      exact Prod.ext x.1.2 x.2.2⟩
  left_inv x := by ext <;> rfl
  right_inv x := by ext <;> rfl

/-- Binary conjugate columns add under direct products. -/
theorem col_prod (A : Type u) (B : Type v) [CommGroup A] [CommGroup B] [Finite A] [Finite B] :
    ∀ k : ℕ, col (A × B) k = col A k + col B k
  | 0 => by
      apply Nat.pow_right_injective (by norm_num : 2 ≤ 2)
      change 2 ^ col (A × B) 0 = 2 ^ (col A 0 + col B 0)
      rw [← card_tors2, pow_add, ← card_tors2, ← card_tors2,
        Nat.card_congr (tors2ProdEquiv A B), Nat.card_prod]
  | k + 1 => by
      rw [col_succ, col_succ, col_succ]
      exact (col_congr k (sqsProdEquiv A B)).trans (col_prod (sqs A) (sqs B) k)

/-- The cyclic group of order four has exponent dividing four. -/
theorem hasExp2_cyclicFour : HasExp2 (Multiplicative (ZMod 4)) 2 := by
  intro x
  apply Multiplicative.toAdd.injective
  change (4 : ℕ) • x.toAdd = 0
  rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

/-- The order of the cyclic-four group. -/
theorem card_cyclicFour : Nat.card (Multiplicative (ZMod 4)) = 4 := by
  rw [Nat.card_congr Multiplicative.toAdd]
  rw [Nat.card_eq_fintype_card]
  exact ZMod.card 4

private def cyclicFourTwo : Multiplicative (ZMod 4) := Multiplicative.ofAdd 2

private theorem cyclicFourTwo_ne_one : cyclicFourTwo ≠ 1 := by
  intro h
  have := congrArg Multiplicative.toAdd h
  change (2 : ZMod 4) = 0 at this
  exact (by decide : (2 : ZMod 4) ≠ 0) this

private theorem cyclicFourTwo_mem_tors2 : cyclicFourTwo ∈
    tors2 (Multiplicative (ZMod 4)) := by
  rw [mem_tors2]
  apply Multiplicative.toAdd.injective
  change (2 : ZMod 4) + 2 = 0
  decide

private theorem cyclicFourTwo_mem_sqs : cyclicFourTwo ∈
    sqs (Multiplicative (ZMod 4)) := by
  refine ⟨Multiplicative.ofAdd 1, ?_⟩
  apply Multiplicative.toAdd.injective
  change (1 : ZMod 4) + 1 = 2
  decide

private theorem two_le_card_tors2_cyclicFour :
    2 ≤ Nat.card (tors2 (Multiplicative (ZMod 4))) := by
  let f : Fin 2 → tors2 (Multiplicative (ZMod 4)) := fun i =>
    if i = 0 then ⟨1, Subgroup.one_mem _⟩ else ⟨cyclicFourTwo, cyclicFourTwo_mem_tors2⟩
  simpa using Nat.card_le_card_of_injective f (by
    intro i j hij
    by_cases hi : i = 0
    · subst i
      by_cases hj : j = 0
      · exact hj.symm
      · have hval := congrArg Subtype.val hij
        simp [f, hj] at hval
        exact (cyclicFourTwo_ne_one hval.symm).elim
    · by_cases hj : j = 0
      · subst j
        have hval := congrArg Subtype.val hij
        simp [f, hi] at hval
        exact (cyclicFourTwo_ne_one hval).elim
      · apply Fin.ext
        omega)

private theorem two_le_card_sqs_cyclicFour :
    2 ≤ Nat.card (sqs (Multiplicative (ZMod 4))) := by
  let f : Fin 2 → sqs (Multiplicative (ZMod 4)) := fun i =>
    if i = 0 then ⟨1, Subgroup.one_mem _⟩ else ⟨cyclicFourTwo, cyclicFourTwo_mem_sqs⟩
  simpa using Nat.card_le_card_of_injective f (by
    intro i j hij
    by_cases hi : i = 0
    · subst i
      by_cases hj : j = 0
      · exact hj.symm
      · have hval := congrArg Subtype.val hij
        simp [f, hj] at hval
        exact (cyclicFourTwo_ne_one hval.symm).elim
    · by_cases hj : j = 0
      · subst j
        have hval := congrArg Subtype.val hij
        simp [f, hi] at hval
        exact (cyclicFourTwo_ne_one hval).elim
      · apply Fin.ext
        omega)

private theorem card_tors2_cyclicFour :
    Nat.card (tors2 (Multiplicative (ZMod 4))) = 2 := by
  have hprod := card_eq_tors2_mul_sqs (Multiplicative (ZMod 4))
  rw [card_cyclicFour] at hprod
  have hs := two_le_card_sqs_cyclicFour
  have ht := two_le_card_tors2_cyclicFour
  have hupper : Nat.card (tors2 (Multiplicative (ZMod 4))) ≤ 2 := by nlinarith
  omega

private theorem card_sqs_cyclicFour :
    Nat.card (sqs (Multiplicative (ZMod 4))) = 2 := by
  have hprod := card_eq_tors2_mul_sqs (Multiplicative (ZMod 4))
  rw [card_cyclicFour] at hprod
  have hs := two_le_card_sqs_cyclicFour
  have ht := two_le_card_tors2_cyclicFour
  have hupper : Nat.card (sqs (Multiplicative (ZMod 4))) ≤ 2 := by nlinarith
  omega

/-- The first two binary columns of `C₄` have total size two. -/
theorem col_zero_add_one_cyclicFour :
    col (Multiplicative (ZMod 4)) 0 + col (Multiplicative (ZMod 4)) 1 = 2 := by
  apply Nat.pow_right_injective (by norm_num : 2 ≤ 2)
  change 2 ^ (col (Multiplicative (ZMod 4)) 0 +
    col (Multiplicative (ZMod 4)) 1) = 2 ^ 2
  rw [← card_quotient_powSub_four]
  have hbot : powSub (Multiplicative (ZMod 4)) 4 = ⊥ := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact hasExp2_cyclicFour y
    · intro hx
      rw [Subgroup.mem_bot] at hx
      subst x
      exact Subgroup.one_mem _
  rw [hbot, Nat.card_congr QuotientGroup.quotientBot.toEquiv, card_cyclicFour]

/-- The first binary column of `C₄` is one. -/
theorem col_zero_cyclicFour : col (Multiplicative (ZMod 4)) 0 = 1 := by
  apply Nat.pow_right_injective (by norm_num : 2 ≤ 2)
  change 2 ^ col (Multiplicative (ZMod 4)) 0 = 2 ^ 1
  rw [← card_quotient_powSub_two]
  have hcard : Nat.card ((Multiplicative (ZMod 4)) ⧸
      powSub (Multiplicative (ZMod 4)) 2) = 2 := by
    have hc := card_cyclicFour
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      (powSub (Multiplicative (ZMod 4)) 2), show powSub
        (Multiplicative (ZMod 4)) 2 = sqs (Multiplicative (ZMod 4)) by rfl,
      card_sqs_cyclicFour] at hc
    have hpos : 0 < Nat.card ((Multiplicative (ZMod 4)) ⧸
        sqs (Multiplicative (ZMod 4))) := Nat.card_pos
    change Nat.card ((Multiplicative (ZMod 4)) ⧸
      sqs (Multiplicative (ZMod 4))) = 2
    omega
  rw [hcard]

/-- The second binary column of `C₄` is one. -/
theorem col_one_cyclicFour : col (Multiplicative (ZMod 4)) 1 = 1 := by
  have hsum := col_zero_add_one_cyclicFour
  have hzero := col_zero_cyclicFour
  omega

/-- Every later binary column of `C₄` vanishes. -/
theorem col_cyclicFour_of_two_le {k : ℕ} (hk : 2 ≤ k) :
    col (Multiplicative (ZMod 4)) k = 0 := by
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hk
  subst k
  clear hk
  rw [show 2 + j = (j + 1) + 1 by omega, col_succ,
    show j + 1 = j + 1 by rfl, col_succ]
  have hsq : sqs (sqs (Multiplicative (ZMod 4))) = ⊥ := by
    ext x
    constructor
    · intro hx
      let y := Classical.choose hx
      have hy := Classical.choose_spec hx
      let z := Classical.choose y.2
      have hz := Classical.choose_spec y.2
      apply Subtype.ext
      calc
        (x.1 : Multiplicative (ZMod 4)) = (y : sqs (Multiplicative (ZMod 4))) ^ 2 :=
          (congrArg Subtype.val hy).symm
        _ = ((z : Multiplicative (ZMod 4)) ^ 2) ^ 2 := by
          change z ^ 2 = (y : Multiplicative (ZMod 4)) at hz
          rw [← hz]
        _ = 1 := by rw [← pow_mul]; exact hasExp2_cyclicFour z
    · intro hx
      rw [Subgroup.mem_bot] at hx
      subst x
      exact Subgroup.one_mem _
  rw [hsq]
  let B : Type := (⊥ : Subgroup (sqs (Multiplicative (ZMod 4))))
  letI : CommGroup B := inferInstance
  letI : Finite B := inferInstance
  letI : Subsingleton B := ⟨fun x y => Subtype.ext
    ((Subgroup.mem_bot.mp x.2).trans (Subgroup.mem_bot.mp y.2).symm)⟩
  change col B j = 0
  have hzero : col B 0 = 0 := by
    rw [col_zero, Nat.card_of_subsingleton (1 : tors2 B)]
    norm_num
  induction j with
  | zero => exact hzero
  | succ j ih =>
      exact Nat.eq_zero_of_le_zero ((col_succ_le B j).trans (by rw [ih]))

/-- Every column of a finite subsingleton commutative group vanishes. -/
theorem col_eq_zero_of_subsingleton (A : Type u) [CommGroup A] [Finite A]
    [Subsingleton A] (k : ℕ) : col A k = 0 := by
  have hzero : col A 0 = 0 := by
    rw [col_zero, Nat.card_of_subsingleton (1 : tors2 A)]
    norm_num
  induction k with
  | zero => exact hzero
  | succ k ih =>
      exact Nat.eq_zero_of_le_zero ((col_succ_le A k).trans (by rw [ih]))

/-- Split the first coordinate from a finite tuple. -/
def piFinSuccMulEquiv (A : Type u) [CommGroup A] (r : ℕ) :
    (Fin (r + 1) → A) ≃* A × (Fin r → A) where
  toFun f := (f 0, fun i => f i.succ)
  invFun x := Fin.cases x.1 x.2
  left_inv f := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl
  right_inv x := by ext <;> rfl
  map_mul' _ _ := rfl

/-- The two first columns of a product of `r` copies of `C₄` are `r`, and
all later columns vanish. -/
theorem col_pi_cyclicFour (r k : ℕ) :
    col (Fin r → Multiplicative (ZMod 4)) k = if k < 2 then r else 0 := by
  induction r with
  | zero =>
      haveI : Subsingleton (Fin 0 → Multiplicative (ZMod 4)) :=
        ⟨fun f g => funext fun i => Fin.elim0 i⟩
      simp [col_eq_zero_of_subsingleton]
  | succ r ih =>
      rw [col_congr k (piFinSuccMulEquiv (Multiplicative (ZMod 4)) r),
        col_prod, ih]
      by_cases hk0 : k = 0
      · subst k
        rw [col_zero_cyclicFour]
        simp [Nat.add_comm]
      · by_cases hk1 : k = 1
        · subst k
          rw [col_one_cyclicFour]
          simp [Nat.add_comm]
        · have hk : 2 ≤ k := by omega
          rw [col_cyclicFour_of_two_le hk]
          simp [show ¬k < 2 by omega]

/-- Columns of the literal auxiliary group used by the marked moment. -/
theorem col_cyclicFourCoordinates (r k : ℕ) :
    col (Multiplicative (Fin r → ZMod 4)) k = if k < 2 then r else 0 := by
  rw [col_congr k (MulEquiv.piMultiplicative (fun _ : Fin r => ZMod 4))]
  exact col_pi_cyclicFour r k

end MarkedC4
end SymmetricSubgroupAsymptotics

end
