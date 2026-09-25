import SymmetricSubgroupAsymptotics.NormalChiefSeries
import Mathlib.FieldTheory.Finiteness
import Mathlib.Data.Nat.Factorization.Basic

/-! Explicit weights of actual chief factors: retain the ternary valuation
only for abelian factors. Nonabelian factors have zero weight, regardless
of their order. The weight equals the original elementary ternary fibre
dimension. No group-order valuation is substituted for a composition count. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

def chiefTernaryWeight (Q:Type) [Group Q] : ℕ := by
  classical
  exact if IsMulCommutative Q then (Nat.card Q).factorization 3 else 0

theorem chiefTernaryWeight_nonabelian (Q:Type) [Group Q] (hn:¬IsMulCommutative Q) :
    chiefTernaryWeight Q=0 := by simp [chiefTernaryWeight,hn]

theorem chiefTernaryWeight_coprime (Q:Type) [Group Q]
    (hc:Nat.Coprime (Nat.card Q) 3) : chiefTernaryWeight Q=0 := by
  have hd : ¬3∣Nat.card Q := Nat.prime_three.coprime_iff_not_dvd.mp hc.symm
  simp [chiefTernaryWeight,Nat.factorization_eq_zero_of_not_dvd hd]

theorem chiefTernaryWeight_elementary {Q V:Type} [Group Q]
    [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    (e:Q≃*Multiplicative V) : chiefTernaryWeight Q=Module.finrank (ZMod 3) V := by
  have hcom : IsMulCommutative Q := ⟨⟨fun x y=>e.injective (by
    rw [map_mul,map_mul,mul_comm])⟩⟩
  have he : Nat.card Q=Nat.card V := Nat.card_congr e.toEquiv
  rw [chiefTernaryWeight,if_pos hcom,he,
    Module.natCard_eq_pow_finrank (K:=ZMod 3),Nat.card_zmod,
    Nat.factorization_pow_self Nat.prime_three]

def actualChiefSeriesTernaryWeight {R:Type} [Group R] (s:ActualChiefSeries R) : ℕ :=
  ∑i:Fin s.length,chiefTernaryWeight (normalChainQuotient
    (s.subgroup i.castSucc) (s.subgroup i.succ))

end SymmetricSubgroupAsymptotics
