import SymmetricSubgroupAsymptotics.FiniteLinearPlaneClassBound
import SymmetricSubgroupAsymptotics.SmallFourPointOrdinaryGenerators
import SymmetricSubgroupAsymptotics.FiniteGroupBinaryOrderGenerators

/-! Ordinary generation on an actual nine-element ternary plane. The
literal projective action has four points and a scalar kernel of order
at most two. The argument uses no catalogue or permutation-generator
input beyond the internally proved four-point theorem. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TernaryLinearPlaneOrdinaryGenerators
open FiniteLinearPlaneClassBound

variable {V H N : Type} [AddCommGroup V] [Module Scalar V]
    [Group H] [Finite H] [Finite V]

theorem genRank_le_three (ρ : H →* (V ≃ₗ[Scalar] V))
    (hV : Nat.card V=9) (hρ : Function.Injective ρ) :
    MarkedC4.genRank H ≤ 3 := by
  let f := pointHom ρ
  have hk : MarkedC4.genRank f.ker ≤ 1 :=
    FiniteGroupBinaryOrderGenerators.genRank_le_of_card_le_two_pow f.ker 1
      (by simpa only [pow_one] using pointHom_kernel_card_le_two ρ hV hρ)
  have hr : MarkedC4.genRank f.range ≤ 2 :=
    SmallFourPointOrdinaryGenerators.genRank_le_two
      (G := f.range) (X := Projectivization Scalar V) (projective_card hV)
  have hq : MarkedC4.genRank (H ⧸ f.ker) ≤ 2 := by
    rw [CoprimeNilpotentProductGenerators.genRank_mulEquiv
      (QuotientGroup.quotientKerEquivRange f)]
    exact hr
  have h := MarkedC4.genRank_le_of_normal f.ker
  omega

variable [Group N]

omit [Finite V] in
def coordinateAut (e : N ≃* Multiplicative V) :
    MulAut N →* (V ≃ₗ[Scalar] V) where
  toFun a := { AddEquiv.toMultiplicative.symm ((MulAut.congr e) a) with
    map_smul' := fun c x => ZMod.map_smul
      (AddEquiv.toMultiplicative.symm ((MulAut.congr e) a)) c x }
  map_one' := by ext x; simp only [map_one]; rfl
  map_mul' _ _ := by ext x; simp only [map_mul]; rfl

omit [Finite V] in
theorem coordinateAut_injective (e : N ≃* Multiplicative V) :
    Function.Injective (coordinateAut e) := by
  intro a b he
  apply (MulAut.congr e).injective
  apply MulEquiv.ext
  intro x
  exact congrArg Multiplicative.ofAdd (DFunLike.congr_fun he x.toAdd)

theorem genRank_le_three_of_faithful_aut (e : N ≃* Multiplicative V)
    (hV : Nat.card V=9) (φ : H →* MulAut N) (hφ : Function.Injective φ) :
    MarkedC4.genRank H ≤ 3 :=
  genRank_le_three ((coordinateAut e).comp φ) hV ((coordinateAut_injective e).comp hφ)

end SymmetricSubgroupAsymptotics.TernaryLinearPlaneOrdinaryGenerators
