import SymmetricSubgroupAsymptotics.PrimitiveSocleElevenPointTitsExclusion
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOuterSaving

/-! The SAME actual positive derived Sylow has at least2048 elements.
Its p-group cardinality and injective image through the FULL central
quotient imply2048 divides the original Tits model's cardinality. Since
2048 does not divide13!, every faithful action has degree at least14.
No known model order, index table, simplicity or outer bound is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleThirteenPointTitsExclusion
open PrimitiveSocleRawStructure CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourDerivedAmbientHom CFSGReeFFourAllParameterDerivedPositive
open CFSGReeFFourBinaryOuterSaving
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance derived_finite : Finite (commutator (originalModelFixed 0)) :=
  Finite.of_injective (derivedAmbientHom 0) (derivedAmbientHom_injective 0)

theorem binary_eleven_dvd_order : 2048 ∣ Nat.card CFSG.Models.Tits := by
  have hp : IsPGroup 2 (derivedPositive 0) :=
    (positiveSylow 0).isPGroup'.of_equiv (MulEquiv.subgroupCongr (positiveSylow_coe 0))
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hp
  have hle : 2 ^ 11 ≤ 2 ^ a := by
    simpa only [ha] using derivedPositive_card_ge_2048
  have h11 : 11 ≤ a :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hle
  have hd : 2048 ∣ Nat.card (derivedPositive 0) := by
    rw [ha]
    exact Nat.pow_dvd_pow 2 h11
  exact hd.trans (Subgroup.card_dvd_of_injective titsPositiveHom titsPositiveHom_injective)

theorem fourteen_le_card_of_injective {X : Type} [Finite X]
    (f : CFSG.Models.Tits →* Equiv.Perm X) (hf : Function.Injective f) :
    14 ≤ Nat.card X := by
  have hd : Nat.card CFSG.Models.Tits ∣ (Nat.card X).factorial := by
    simpa only [Nat.card_perm] using Subgroup.card_dvd_of_injective f hf
  by_contra hsmall
  have h2048 : 2048 ∣ Nat.factorial 13 := binary_eleven_dvd_order.trans
    (hd.trans (Nat.factorial_dvd_factorial (by omega)))
  exact (by decide : ¬ 2048 ∣ Nat.factorial 13) h2048

theorem not_tits_of_degree_le_thirteen
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (D : NonaffineData G X) (hdegree : Nat.card X ≤ 13)
    (e : D.Simple ≃* CFSG.Models.Tits) : False := by
  have hd := PrimitiveSocleElevenPointTitsExclusion.simple_card_dvd_degree_factorial D
  rw [Nat.card_congr e.toEquiv] at hd
  have h2048 : 2048 ∣ Nat.factorial 13 := binary_eleven_dvd_order.trans
    (hd.trans (Nat.factorial_dvd_factorial hdegree))
  exact (by decide : ¬ 2048 ∣ Nat.factorial 13) h2048

end SymmetricSubgroupAsymptotics.PrimitiveSocleThirteenPointTitsExclusion
