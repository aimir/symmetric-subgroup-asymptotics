import SymmetricSubgroupAsymptotics.Non2PreE7SmallAdditiveTemplate

/-! The existing derived-cyclic-dual theorem gives the sharp cubic top
factor directly from Kovács--Praeger on the literal derived subgroup. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
variable {T : Type} [Group T] [Finite T]

 theorem derived_cubic_top_epi_envelope (D : DerivedCyclicDual T 3)
    (hKP : KovacsPraegerAbelianizationBound) (b : ℕ)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J T) : ℝ) ≤
      (Nat.card (T ≃* T) : ℝ)*(3 : ℝ)^((b : ℝ)/3) := by
  have h := D.epi_card_le (J := J)
  have hc := cyclicCharacter_card_le_abelianization (commutator J) 3
  have hk := derived_abelianization_le hKP J
  have hcReal : (Nat.card (commutator J →* Multiplicative (ZMod 3)) : ℝ)≤
      (Nat.card (Abelianization (commutator J)) : ℝ) := by exact_mod_cast hc
  have hc' : (Nat.card (commutator J →* Multiplicative (ZMod 3)) : ℝ) ≤
      (3 : ℝ)^((b : ℝ)/3) :=
    hcReal.trans hk
  have h' : (Nat.card (GroupEpimorphism J T) : ℝ) ≤
      (Nat.card (commutator J →* Multiplicative (ZMod 3)) : ℝ)*
        (Nat.card (T ≃* T) : ℝ) := by exact_mod_cast h
  have hm := mul_le_mul_of_nonneg_right hc' (Nat.cast_nonneg (Nat.card (T ≃* T)))
  exact h'.trans (hm.trans_eq (mul_comm _ _))

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
