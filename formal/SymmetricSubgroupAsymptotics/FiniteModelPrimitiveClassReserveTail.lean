import SymmetricSubgroupAsymptotics.FiniteModelPrimitiveClassTail

/-! Every fixed finite simple-model family pays any fixed additive class
reserve above one degree threshold. The same actual D and arbitrary
subgroup H are retained; no order, class or generator table is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.FiniteModelPrimitiveClassReserveTail
open PrimitiveSocleRawStructure CFSGReduction

theorem four_pow_le_five_reserve (c n : ℕ) (hn : 8*c≤n) :
    4^n≤5^(n-c) := by
  induction c generalizing n with
  | zero => simpa only [Nat.sub_zero] using Nat.pow_le_pow_left (by decide : 4≤5) n
  | succ c ih =>
      have hsmall : 8*c≤n-8 := by omega
      calc
        4^n=4^(n-8)*4^8 := by rw [←pow_add]; congr 1; omega
        _≤5^((n-8)-c)*5^7 := Nat.mul_le_mul (ih (n-8) hsmall) (by decide)
        _=5^(n-(c+1)) := by rw [←pow_add]; congr 1; omega

theorem order_cube_le_four (n : ℕ) (hn : 1024≤n) :
    (n^(4*Nat.log 2 n+2))^3≤4^(n-1) := by
  let l := Nat.log 2 n
  have hl : 10≤l := Nat.le_log_of_pow_le (by decide : 1<2) (by simpa using hn)
  have hupper : n≤2^(l+1) := (Nat.lt_pow_succ_log_self (by decide : 1<2) n).le
  have hlower : 2^l≤n := Nat.pow_log_le_self 2 (by omega)
  have hsmall := LogSquareOrderClassNumerics.dyadic_exponent_le l hl
  have he : 3*(l+1)*(4*l+2)≤2*(n-1) := by omega
  calc
    (n^(4*Nat.log 2 n+2))^3≤((2^(l+1))^(4*l+2))^3 :=
      Nat.pow_le_pow_left (Nat.pow_le_pow_left hupper _) _
    _=2^(3*(l+1)*(4*l+2)) := by rw [←pow_mul,←pow_mul]; congr 1; ring
    _≤2^(2*(n-1)) := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) he
    _=4^(n-1) := by rw [pow_mul]; norm_num

theorem subgroup_class_cube_le_of_order {G : Type} [Group G] [Finite G]
    (n c : ℕ) (hn : 1024≤n) (hc : 8*c≤n)
    (horder : Nat.card G≤n^(4*Nat.log 2 n+2)) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3≤5^(n-c) := by
  have hclasses : Nat.card (ConjClasses H)≤n^(4*Nat.log 2 n+2) :=
    (Nat.card_le_card_of_surjective (@ConjClasses.mk H _) ConjClasses.mk_surjective).trans
      (H.card_le_card_group.trans horder)
  exact (Nat.pow_le_pow_left hclasses 3).trans ((order_cube_le_four n hn).trans
    ((Nat.pow_le_pow_right (by decide : 0<(4:ℕ)) (Nat.sub_le n 1)).trans
      (four_pow_le_five_reserve c n hc)))

def PaysModel (M : Type) [Group M] (c N : ℕ) : Prop :=
  ∀ {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X), (D.Simple ≃* M) → N≤Nat.card X →
      ∀ H : Subgroup G,Nat.card (ConjClasses H)^3≤5^(Nat.card X-c)

theorem pays_of_finite (M : Type) [Group M] [Finite M] (c : ℕ) :
    PaysModel M c (max 1024 (max (8*c) (Nat.card M*Nat.card (Outer M)))) := by
  intro G X _ _ _ _ D e hn H
  have hlarge : 1024≤Nat.card X := (le_max_left _ _).trans hn
  have hrest : max (8*c) (Nat.card M*Nat.card (Outer M))≤Nat.card X :=
    (le_max_right _ _).trans hn
  apply subgroup_class_cube_le_of_order (Nat.card X) c hlarge
    ((le_max_left _ _).trans hrest) _ H
  apply FiniteModelPrimitiveClassTail.order_le_degree_log_square D
  · rw [Nat.card_congr e.toEquiv,outer_card_congr e]
    exact (le_max_right _ _).trans hrest
  · omega

theorem exists_threshold (M : Type) [Group M] (c : ℕ) : ∃ N,PaysModel M c N := by
  by_cases h : Finite M
  · letI := h
    exact ⟨_,pays_of_finite M c⟩
  · refine ⟨0,?_⟩
    intro G X _ _ _ _ D e hn H
    exact (h (Finite.of_equiv D.Simple e.toEquiv)).elim

theorem pays_mono {M : Type} [Group M] {c N N' : ℕ}
    (h : PaysModel M c N) (hNN : N≤N') : PaysModel M c N' := by
  intro G X _ _ _ _ D e hn H
  exact h D e (hNN.trans hn) H

theorem finite_family_threshold {ι : Type} [Finite ι]
    (M : ι → Type) [∀ i,Group (M i)] (c : ℕ) :
    ∃ N,∀ i,PaysModel (M i) c N := by
  letI := Fintype.ofFinite ι
  choose N hN using fun i => exists_threshold (M i) c
  refine ⟨Finset.univ.sup N,?_⟩
  intro i
  exact pays_mono (hN i) (Finset.le_sup (Finset.mem_univ i))

end SymmetricSubgroupAsymptotics.FiniteModelPrimitiveClassReserveTail
