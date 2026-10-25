import SymmetricSubgroupAsymptotics.PrimitiveSocleAllFactorProperClassGap

/-! A shared order-at-index packet suffices for the proper-subnormal
extra exponent. The same literal K is retained, and K=bot supplies the
simple-order threshold needed for the power-form branch. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.proper_subnormal_class_cube_le_of_large_index_order_budget
    (D : NonaffineData G X) (hdegree : 2 ≤ Nat.card X)
    (hindex : ∀ K : Subgroup D.Simple, K ≠ ⊤ → 1024 ≤ K.index)
    (horder : ∀ K : Subgroup D.Simple, K ≠ ⊤ →
      Nat.card D.Simple*Nat.card (Outer D.Simple) ≤ K.index^66)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  have hlarge : 1024 ≤ Nat.card D.Simple := by
    simpa only [Subgroup.index_bot] using
      hindex ⊥ (bot_ne_top : (⊥ : Subgroup D.Simple) ≠ ⊤)
  apply D.proper_subnormal_class_cube_le_of_order_index_budget hdegree hlarge _ H hH hne
  intro K hK
  have hi := hindex K hK
  have hn := BoundedComponentSocleClassNumerics.component_cube_le_garonziMaroti
    K.index 1 (by omega) (by decide) (by simpa only [pow_one] using hi)
  simp only [pow_one, Nat.factorial_one, mul_one] at hn
  exact (Nat.pow_le_pow_left (horder K hK) 3).trans hn

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
