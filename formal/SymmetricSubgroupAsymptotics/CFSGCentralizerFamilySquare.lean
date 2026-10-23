import SymmetricSubgroupAsymptotics.CFSGSimpleConjugateFamilyIndex

/-! A relative-root family needs no exact Sylow order formula. Its orbit
charge and a centralizer larger than the number of Weyl representatives
give a strict square bound directly from two disjoint Sylow images. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGCentralizerFamilySquare

theorem family_lt_sylow (M c R u : ℕ) (hu : 0 < u) (hR : R < c)
    (hM : M*c ≤ R*u) : M < u := by
  have hr := Nat.mul_lt_mul_of_pos_right hR hu
  have hprod : M*c < u*c := by
    exact hM.trans_lt (by simpa only [Nat.mul_comm c u] using hr)
  nlinarith

theorem square_lt_of_double_sylow_and_centralizer (M c R u B : ℕ)
    (hu : 0 < u) (hR : R < c) (hM : M*c ≤ R*u) (hB : u^2 ≤ B) : M^2 < B := by
  have hlt := family_lt_sylow M c R u hu hR hM
  have hs : M^2 < u^2 := by nlinarith
  exact hs.trans_le hB

theorem family_le_sylow (M c R u : ℕ) (hc : 0 < c) (hR : R ≤ c)
    (hM : M*c ≤ R*u) : M ≤ u := by
  have hprod : M*c ≤ u*c :=
    hM.trans (by simpa only [Nat.mul_comm c u] using Nat.mul_le_mul_right u hR)
  exact Nat.le_of_mul_le_mul_right hprod hc

theorem square_lt_of_strict_double_sylow_and_centralizer (M c R u B : ℕ)
    (hc : 0 < c) (hR : R ≤ c) (hM : M*c ≤ R*u) (hB : u^2 < B) : M^2 < B := by
  have hle := family_le_sylow M c R u hc hR hM
  have hs : M^2 ≤ u^2 := by nlinarith
  exact hs.trans_lt hB

end SymmetricSubgroupAsymptotics.CFSGCentralizerFamilySquare
