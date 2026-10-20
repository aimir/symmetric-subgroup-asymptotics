import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeEightLinearEmbedding
import SymmetricSubgroupAsymptotics.PrimitiveAffinePublishedSmallStructuralInput
import SymmetricSubgroupAsymptotics.PrimitiveCompositionLengthInput
import SymmetricSubgroupAsymptotics.SolubleCompositionPrimeFactorLength
import SymmetricSubgroupAsymptotics.DegreeEightyOneDivisorBudget
import SymmetricSubgroupAsymptotics.RepeatedMarkerProfileBound
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-! The needed degree-81 soluble-complement cube follows from the retained
primitive composition theorem and the exact elementary GL(4,3) order.
It does not require the general soluble linear base theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical IsMulCommutative
attribute [local instance] Fintype.ofFinite
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu

theorem primitiveAffineEightyOne_complement_le_cube
    (hcomp : PrimitiveCompositionLengthInput)
    (U : PreE7NonPairActionClass 81)
    (P : PrimitiveAffineProfile (preE7NonPairAction 81 U) (Fin 81))
    (hprimitive : MulAction.IsPreprimitive (preE7NonPairAction 81 U) (Fin 81))
    (x : Fin 81) (hsolvable : IsSolvable (P.complement x)) :
    Nat.card (P.complement x) ≤ 81^3 := by
  let G := preE7NonPairAction 81 U
  letI := hprimitive
  let C := P.elementaryChart hprimitive
  letI : Fact P.p.Prime := C.primeFact
  letI : AddCommGroup C.V := C.addCommGroup
  letI : Module (ZMod P.p) C.V := C.module
  letI : FiniteDimensional (ZMod P.p) C.V := C.finiteDimensional
  letI : Nontrivial C.V := C.nontrivial
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v)) C.equiv.symm.injective
  have hpower : P.p^C.d=3^4 := by
    simpa only [Nat.card_fin,show 3^4=81 by decide] using
      (P.degree_eq_prime_pow_finrank C.equiv x).symm
  have hpd : P.p∣3 := P.p_prime.dvd_of_dvd_pow (by
    rw [← hpower]
    exact dvd_pow_self P.p C.d_pos.ne')
  have h3d : 3∣P.p := Nat.prime_three.dvd_of_dvd_pow (by
    rw [hpower]
    exact dvd_pow_self 3 (by decide : (4 : ℕ)≠0))
  have hp : P.p=3 := Nat.dvd_antisymm hpd h3d
  have hdim : Module.finrank (ZMod P.p) C.V=4 := by
    change C.d=4
    rw [hp] at hpower
    exact Nat.pow_right_injective (by decide : 2≤3) hpower
  let basis := Module.finBasisOfFinrankEq (ZMod P.p) C.V hdim
  let rho := (P.complementRepresentationCore hprimitive C x).ρ
  let phi : P.complement x →* Matrix.GeneralLinearGroup (Fin 4) (ZMod P.p) :=
    (Matrix.GeneralLinearGroup.toLin' basis).symm.toMonoidHom.comp
      (Representation.asGroupHom rho)
  have hphi : Function.Injective phi := by
    intro a b hab
    apply P.complementRepresentationCore_injective hprimitive C x
    have he : Representation.asGroupHom rho a=Representation.asGroupHom rho b :=
      (Matrix.GeneralLinearGroup.toLin' basis).symm.injective hab
    exact congrArg Units.val he
  have hgl : Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod P.p))=24261120 := by
    rw [Matrix.card_GL_field]
    norm_num [ZMod.card,hp,Fin.prod_univ_succ]
  have hdvd : Nat.card (P.complement x)∣24261120 :=
    hgl ▸ Subgroup.card_dvd_of_injective phi hphi
  letI : Group.IsNilpotent P.V := P.V_pgroup.isNilpotent
  letI : IsSolvable (P.complement x) := hsolvable
  letI : IsSolvable G := solvable_of_ker_le_range P.V.subtype (P.complementProjection x) (by
    rw [P.complementProjection_ker x,Subgroup.range_subtype])
  obtain ⟨t,_,_,_,_⟩ := actualChiefSeries_composition_refinement (actualChiefSeries G)
  have hco := hcomp 81 (by decide) (preE7NonPairAction 81 U) hprimitive t
  have hlog : Real.logb 2 (81 : ℝ)=4*Real.logb 2 3 := by
    rw [show (81 : ℝ)=3^4 by norm_num,Real.logb_pow]
    norm_num
  have hlt : (t.chain.length : ℝ)<16 := by
    change (t.chain.length : ℝ) ≤ (8/3 : ℝ)*Real.logb 2 (81 : ℝ)-4/3 at hco
    rw [hlog] at hco
    linarith [RepeatedMarkerProfileBound.logb_two_three_lt]
  have hlen : t.chain.length≤15 := by
    have hnat : t.chain.length<16 := by exact_mod_cast hlt
    omega
  have hbudget : ArithmeticFunction.cardFactors (Nat.card G)≤15 :=
    (soluble_cardFactors_le_compositionLength t).trans hlen
  have hfactor : Nat.card G=81*Nat.card (P.complement x) := by
    simpa only [P.card_eq x,Nat.card_fin] using (P.isComplement'_complement x).card_mul.symm
  have hmass : ArithmeticFunction.cardFactors (Nat.card G)=
      4+ArithmeticFunction.cardFactors (Nat.card (P.complement x)) := by
    rw [hfactor,ArithmeticFunction.cardFactors_mul (by decide) Nat.card_pos.ne']
    have h81 : ArithmeticFunction.cardFactors 81=4 := by
      rw [show (81 : ℕ)=3^4 by decide,ArithmeticFunction.cardFactors_apply_prime_pow Nat.prime_three]
    rw [h81]
  exact DegreeEightyOneDivisorBudget.order_le_cube _ hdvd (by omega)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
