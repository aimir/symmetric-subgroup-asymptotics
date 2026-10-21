import SymmetricSubgroupAsymptotics.BinaryElementaryActualComparatorSource
import SymmetricSubgroupAsymptotics.RepresentationDualIrreducibleUniform
import SymmetricSubgroupAsymptotics.PrimitiveAffineBottomFibre
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeSixteenCoordinateAction
import SymmetricSubgroupAsymptotics.GeneralFourTwoAlternatingEquiv
import SymmetricSubgroupAsymptotics.FixedColdRankSourceInstallation
import SymmetricSubgroupAsymptotics.WidthSixteenBinaryRankTailResidual

/-! An actual primitive affine16 group has a complete original source via
its irreducible translation kernel and actual eight-point complement.
No soluble-order theorem, nonsoluble chief-length bound, or primitive16
classifier is a premise. All original normal axes remain visible. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineSixteenActualColdSource

variable {U : PreE7NonPairActionClass 16}
    (P : PrimitiveAffineProfile (preE7NonPairAction 16 U) (Fin 16))

include P in
def binaryProfile
    (hp : MulAction.IsPreprimitive (preE7NonPairAction 16 U) (Fin 16)) :
    PrimitiveAffineProfile (preE7NonPairAction 16 U) (Fin 16) where
  p := 2
  p_prime := by decide
  V := P.V
  V_normal := P.V_normal
  V_pgroup := by rw [←(P.degreeSixteen_prime_dimension hp 0 (by simp)).1]; exact P.V_pgroup
  regular := P.regular

theorem order_budgets
    (hp : MulAction.IsPreprimitive (preE7NonPairAction 16 U) (Fin 16)) (x : Fin 16) :
    Nat.card (preE7NonPairAction 16 U) ≤ 2^19 ∧ Nat.card (P.complement x) ≤ 2^15 := by
  have hh := Nat.card_le_card_of_injective
    (P.complementLinearMap_degreeSixteen hp x (by simp))
    (P.complementLinearMap_degreeSixteen_injective hp x (by simp))
  rw [GeneralFourTwoMatrixEncoding.ambient_card] at hh
  have hb : Nat.card (P.complement x) ≤ 2^15 := hh.trans (by norm_num)
  have hg : Nat.card (preE7NonPairAction 16 U)=16*Nat.card (P.complement x) := by
    simpa only [P.card_eq x,Nat.card_fin] using (P.isComplement'_complement x).card_mul.symm
  exact ⟨by rw [hg]; exact (Nat.mul_le_mul_left 16 hb).trans (by norm_num),hb⟩

include P in
def data
    (hp : MulAction.IsPreprimitive (preE7NonPairAction 16 U) (Fin 16)) (x : Fin 16) :
    PreE7DegreeTwoPairSummedSource 16 U := by
  let Q := binaryProfile P hp
  let C := Q.elementaryChart hp
  letI : Fact Q.p.Prime := C.primeFact
  letI : AddCommGroup C.V := C.addCommGroup
  letI : Module (ZMod Q.p) C.V := C.module
  letI : FiniteDimensional (ZMod Q.p) C.V := C.finiteDimensional
  let A := Q.complementRepresentation hp C x
  let EC := Q.bottomModuleChart hp C x
  have hu : UniformSubrepresentationGeneratorBound A.ρ.dual 1 :=
    representation_dual_uniform_one_of_irreducible A.ρ
      (Q.complementRepresentation_irreducible hp C x)
  have caps := order_budgets Q hp x
  let action := GeneralFourTwoAlternatingEquiv.eightAction.comp
    (Q.complementLinearMap_degreeSixteen hp x (by simp))
  have hf : Function.Injective action :=
    GeneralFourTwoAlternatingEquiv.eightAction_injective.comp
      (Q.complementLinearMap_degreeSixteen_injective hp x (by simp))
  exact BinaryElementaryActualComparatorSource.data
    (Q.complementProjection x) (Q.complementProjection_surjective x) A EC hu
    19 15 caps.1 caps.2 8 action hf

include P in
def source
    (hp : MulAction.IsPreprimitive (preE7NonPairAction 16 U) (Fin 16)) (x : Fin 16) :
    PreE7RankTailSourceOrYonedaTopData 16 U := by
  let S := data P hp x
  have hparams : PreE7CharacterEntryParameters preE7CharacterRho 16 S.v
      (51/200) (1/100) (201/200) (63/50) 0 := by
    change PreE7CharacterEntryParameters preE7CharacterRho 16 8
      (51/200) (1/100) (201/200) (63/50) 0
    constructor <;> norm_num [preE7CharacterRho,halfDegree]
  let M : S.NumericalMargin := FixedColdRankSourceInstallation.numericalMargin
    S 8 32787 361 646 rfl (by decide) (by decide)
    (51/200) (1/100) (201/200) (63/50)
    rfl rfl (by change (51/200 : ℝ)*(1 : ℕ)=51/200; norm_num) rfl rfl hparams (by
      intro b
      have hh := WidthSixteenBinaryRankTailResidual.two_rpow_hundred_width_le_menuMass
        (w := 16) (by decide) b
      norm_num only [Nat.cast_ofNat] at hh
      have hh' : (2 : ℝ)^(1600 : ℕ) ≤
          (2 : ℝ)^(16*(16 : ℝ)*Real.log ((16+b+2 : ℕ) : ℝ)^2) := by
        calc
          _ = (2 : ℝ)^(100*(16 : ℝ)) := by
            rw [←Real.rpow_natCast]
            congr 1
            norm_num
          _ ≤ _ := by convert hh using 1 <;> norm_num
      exact (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (by decide : 646 ≤ 1600)).trans hh')
  exact .inr (.inr (S.toResidualChoice M))

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineSixteenActualColdSource
