import SymmetricSubgroupAsymptotics.TernaryLinearPlaneOrdinaryGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineOrdinaryGeneratorRank
import SymmetricSubgroupAsymptotics.TraceySharpLogSquareNumerics

/-! The primitive-affine sharp degree-nine row from the actual regular
translation group and literal four-point projective action of its
complement. No primitive catalogue or general generator bound is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineNineOrdinaryGenerators

variable {G X : Type} [Group G] [Finite G] [Finite X] [Nontrivial X]
    [MulAction G X] [FaithfulSMul G X] (P : PrimitiveAffineProfile G X)

include P in
theorem genRank_le_four (hprimitive : MulAction.IsPreprimitive G X)
    (hX : Nat.card X=9) : MarkedC4.genRank G ≤ 4 := by
  let x : X := Classical.choice inferInstance
  have hV : Nat.card P.V=9 := (Nat.card_congr (P.pointEquiv x)).trans hX
  letI : Fact P.p.Prime := ⟨P.p_prime⟩
  have hp9 : P.p ∣ 9 := by
    rcases P.V_pgroup.card_eq_or_dvd with h | h
    · omega
    · simpa only [hV] using h
  have hp3 : P.p ∣ 3 := P.p_prime.dvd_of_dvd_pow
    (show P.p ∣ (3:ℕ)^2 from hp9)
  have hp : P.p=3 := (Nat.prime_dvd_prime_iff_eq P.p_prime Nat.prime_three).mp hp3
  have helem := P.elementary hprimitive
  obtain ⟨V,hadd,hmod,hfd,⟨e⟩⟩ := helem
  letI : AddCommGroup V := hadd
  letI : Module (ZMod 3) V :=
    Eq.mp (congrArg (fun p : ℕ => Module (ZMod p) V) hp) hmod
  letI : Finite V := Finite.of_equiv P.V e.toEquiv
  have hv9 : Nat.card V=9 := (Nat.card_congr e.toEquiv).symm.trans hV
  have hc : MarkedC4.genRank (P.complement x) ≤ 3 :=
    TernaryLinearPlaneOrdinaryGenerators.genRank_le_three_of_faithful_aut e hv9
      (P.complementAction x) (P.complementAction_injective x)
  exact (P.genRank_le_complement_add_one hprimitive x).trans (by omega)

theorem four_le_sharpFloor_nine : 4 ≤ TraceySharpHalfDegreeNumerics.sharpFloor 9 := by
  apply TraceySharpLogSquareNumerics.le_sharpFloor_of_log_square 9 4 (by norm_num)
  have h := TraceySharpLogSquareNumerics.logb_le_half_of_square_le_pow 9 7
    (by norm_num) (by norm_num)
  norm_num only [Nat.cast_ofNat] at h ⊢
  nlinarith

include P in
theorem genRank_le_sharpFloor (hprimitive : MulAction.IsPreprimitive G X)
    (hX : Nat.card X=9) :
    MarkedC4.genRank G ≤ TraceySharpHalfDegreeNumerics.sharpFloor (Nat.card X) := by
  rw [hX]
  exact (genRank_le_four P hprimitive hX).trans four_le_sharpFloor_nine

end SymmetricSubgroupAsymptotics.PrimitiveAffineNineOrdinaryGenerators
