import SymmetricSubgroupAsymptotics.PrimitiveSocleProperSubnormalClassGap

/-! An exact existing product cube at
every proper simple-group index pays BOTH one-factor primitive degree
forms, using the literal K in the index form and K=bot in the power form. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.product_cube_le_of_factor_one_index_budget
    (D : NonaffineData G X) (hk : D.factorCount=1) (B : ℕ)
    (hbudget : ∀ K : Subgroup D.Simple, K ≠ ⊤ → B^3 ≤ 5^(K.index-1)) :
    B^3 ≤ 5^(Nat.card X-1) := by
  rcases D.indexForm with ⟨K, hK, hdegree⟩ | ⟨a, hka, hdegree⟩
  · rw [hk, pow_one] at hdegree
    simpa only [hdegree] using hbudget K hK
  · have ha : a ≠ 0 := by have hp := D.factorCount_pos; omega
    have hcard : Nat.card D.Simple ≤ Nat.card X := by
      rw [hdegree]
      exact Nat.le_self_pow ha _
    have hh := hbudget ⊥ (bot_ne_top : (⊥ : Subgroup D.Simple) ≠ ⊤)
    rw [Subgroup.index_bot] at hh
    exact hh.trans (Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_right hcard 1))

theorem NonaffineData.proper_subnormal_class_cube_le_of_factor_one_index_budget
    (D : NonaffineData G X) (hk : D.factorCount=1) (hdegree : 2 ≤ Nat.card X)
    (hbudget : ∀ K : Subgroup D.Simple, K ≠ ⊤ →
      (Nat.card (ConjClasses D.Simple)*Nat.card (Outer D.Simple))^3 ≤ 5^(K.index-1))
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) :=
  D.proper_subnormal_class_cube_le_of_factor_one hk hdegree
    (D.product_cube_le_of_factor_one_index_budget hk _ hbudget) H hH hne

theorem NonaffineData.proper_subnormal_class_cube_le_of_factor_one_order_index_budget
    (D : NonaffineData G X) (hk : D.factorCount=1) (hdegree : 2 ≤ Nat.card X)
    (hbudget : ∀ K : Subgroup D.Simple, K ≠ ⊤ →
      (Nat.card D.Simple*Nat.card (Outer D.Simple))^3 ≤ 5^(K.index-1))
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) :=
  D.proper_subnormal_class_cube_le_of_factor_one_order hk hdegree
    (D.product_cube_le_of_factor_one_index_budget hk _ hbudget) H hH hne

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
