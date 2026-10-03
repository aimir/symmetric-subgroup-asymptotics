import SymmetricSubgroupAsymptotics.PrimitiveAffineComplementRepresentationCore
import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitivePrimeMargin
import SymmetricSubgroupAsymptotics.PrimitiveAffineBottomFibre
import SymmetricSubgroupAsymptotics.PrimitiveAffineDimensionOrder
import SymmetricSubgroupAsymptotics.PrimitiveAffineMediumOddSource
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Exact order divisors for the remaining small affine components

The refined-capacity argument spends prime multiplicities, so an upper bound
for the component order is insufficient.  The literal point stabilizer acts
faithfully on the translation module.  Choosing a basis embeds it in the
appropriate general linear group, hence its order divides the exact linear
group order.  Together with the regular translation subgroup this gives the
four divisors used by the small-degree numerical theorem.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)

/-- A basis of the literal translation module gives an order divisor for the
whole affine component. -/
theorem component_card_dvd_degree_mul_GL
    (d : ℕ)
    (hr : Nat.card block.Fibre = P.p ^ d) :
    Nat.card block.Component ∣
      Nat.card block.Fibre *
        Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod P.p)) := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  let C := P.elementaryChart block.component_preprimitive
  letI : Fact P.p.Prime := C.primeFact
  letI : AddCommGroup C.V := C.addCommGroup
  letI : Module (ZMod P.p) C.V := C.module
  letI : FiniteDimensional (ZMod P.p) C.V := C.finiteDimensional
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v))
    C.equiv.symm.injective
  letI : Fact P.p.Prime := C.primeFact
  letI : AddCommGroup C.V := C.addCommGroup
  letI : Module (ZMod P.p) C.V := C.module
  letI : FiniteDimensional (ZMod P.p) C.V := C.finiteDimensional
  letI : Nontrivial C.V := C.nontrivial
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v))
    C.equiv.symm.injective
  let x : block.Fibre := ⟨basePoint, block.map_base⟩
  have hd : Module.finrank (ZMod P.p) C.V = d := by
    have hdegree : Nat.card block.Fibre =
        P.p ^ Module.finrank (ZMod P.p) C.V := by
      simpa using P.degree_eq_prime_pow_finrank C.equiv x
    rw [hr] at hdegree
    exact Nat.pow_right_injective P.p_prime.one_lt hdegree.symm
  let basis : Module.Basis (Fin d) (ZMod P.p) C.V :=
    Module.finBasisOfFinrankEq (ZMod P.p) C.V hd
  let rho := (P.complementRepresentationCore
    block.component_preprimitive C x).ρ
  let phi : P.complement x →*
      Matrix.GeneralLinearGroup (Fin d) (ZMod P.p) :=
    (Matrix.GeneralLinearGroup.toLin' basis).symm.toMonoidHom.comp
      (Representation.asGroupHom rho)
  have hphi : Function.Injective phi := by
    intro a b hab
    apply P.complementRepresentationCore_injective
      block.component_preprimitive C x
    have hab' : Representation.asGroupHom rho a =
        Representation.asGroupHom rho b := by
      exact (Matrix.GeneralLinearGroup.toLin' basis).symm.injective (by
        simpa [phi] using hab)
    exact congrArg Units.val hab'
  have hcomp : Nat.card (P.complement x) ∣
      Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod P.p)) :=
    Subgroup.card_dvd_of_injective phi hphi
  have hfactor := (P.isComplement'_complement x).card_mul
  have hV : Nat.card P.V = Nat.card block.Fibre := P.card_eq x
  rw [hfactor.symm, hV]
  exact Nat.mul_dvd_mul_left (Nat.card block.Fibre) hcomp

private theorem affine_prime_dimension
    (r p d : ℕ) (hr : Nat.card block.Fibre = r)
    (hp : P.p = p) (hd : r = p ^ d) :
    Nat.card block.Fibre = P.p ^ d := by
  calc
    Nat.card block.Fibre = r := hr
    _ = p ^ d := hd
    _ = P.p ^ d := by rw [hp]

include P

/-- Every degree-two primitive affine component is the regular `C₂`, so its
order divides `2 |GL₁(2)| = 2`. -/
theorem component_card_dvd_2
    (hr : Nat.card block.Fibre = 2) :
    Nat.card block.Component ∣ 2 := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  let C := P.elementaryChart block.component_preprimitive
  letI : Fact P.p.Prime := C.primeFact
  letI : AddCommGroup C.V := C.addCommGroup
  letI : Module (ZMod P.p) C.V := C.module
  letI : FiniteDimensional (ZMod P.p) C.V := C.finiteDimensional
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v))
    C.equiv.symm.injective
  have hdegree0 : Nat.card block.Fibre = P.p ^ C.d := by
    simpa [PrimitiveAffineProfile.ElementaryChart.d] using
      P.degree_eq_prime_pow_finrank C.equiv
        ⟨basePoint, block.map_base⟩
  have hdegree : 2 = P.p ^ C.d := hr.symm.trans hdegree0
  have hpd := prime_pow_positive_injective (d := C.d) (e := 1)
    P.p_prime Nat.prime_two C.d_pos (by norm_num)
      (hdegree.symm.trans (by norm_num))
  have hp : P.p = 2 := hpd.1
  have hdiv := component_card_dvd_degree_mul_GL block P 1
    (affine_prime_dimension block P 2 2 1 hr hp (by norm_num))
  have hcard : Nat.card
      (Matrix.GeneralLinearGroup (Fin 1) (ZMod P.p)) = 1 := by
    rw [Matrix.card_GL_field, ZMod.card]
    norm_num [hp]
  simpa only [hr, hcard, mul_one] using hdiv

/-- Every degree-three primitive affine component has order dividing
`3 |GL₁(3)| = 6`. -/
theorem component_card_dvd_6
    (hr : Nat.card block.Fibre = 3) :
    Nat.card block.Component ∣ 6 := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  let C := P.elementaryChart block.component_preprimitive
  letI : Fact P.p.Prime := C.primeFact
  letI : AddCommGroup C.V := C.addCommGroup
  letI : Module (ZMod P.p) C.V := C.module
  letI : FiniteDimensional (ZMod P.p) C.V := C.finiteDimensional
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v))
    C.equiv.symm.injective
  have hdegree0 : Nat.card block.Fibre = P.p ^ C.d := by
    simpa [PrimitiveAffineProfile.ElementaryChart.d] using
      P.degree_eq_prime_pow_finrank C.equiv
        ⟨basePoint, block.map_base⟩
  have hdegree : 3 = P.p ^ C.d := hr.symm.trans hdegree0
  have hpd := prime_pow_positive_injective (d := C.d) (e := 1)
    P.p_prime (by norm_num : Nat.Prime 3) C.d_pos (by norm_num)
      (hdegree.symm.trans (by norm_num))
  have hp : P.p = 3 := hpd.1
  have hdiv := component_card_dvd_degree_mul_GL block P 1
    (affine_prime_dimension block P 3 3 1 hr hp (by norm_num))
  have hcard : Nat.card
      (Matrix.GeneralLinearGroup (Fin 1) (ZMod P.p)) = 2 := by
    rw [Matrix.card_GL_field, ZMod.card]
    norm_num [hp]
  simpa only [hr, hcard] using hdiv

/-- Every degree-four primitive affine component has order dividing
`4 |GL₂(2)| = 24`. -/
theorem component_card_dvd_24
    (hr : Nat.card block.Fibre = 4) :
    Nat.card block.Component ∣ 24 := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  let C := P.elementaryChart block.component_preprimitive
  letI : Fact P.p.Prime := C.primeFact
  letI : AddCommGroup C.V := C.addCommGroup
  letI : Module (ZMod P.p) C.V := C.module
  letI : FiniteDimensional (ZMod P.p) C.V := C.finiteDimensional
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v))
    C.equiv.symm.injective
  have hdegree0 : Nat.card block.Fibre = P.p ^ C.d := by
    simpa [PrimitiveAffineProfile.ElementaryChart.d] using
      P.degree_eq_prime_pow_finrank C.equiv
        ⟨basePoint, block.map_base⟩
  have hdegree : 4 = P.p ^ C.d := hr.symm.trans hdegree0
  have hpd := prime_pow_positive_injective (d := C.d) (e := 2)
    P.p_prime Nat.prime_two C.d_pos (by norm_num)
      (hdegree.symm.trans (by norm_num))
  have hp : P.p = 2 := hpd.1
  have hdiv := component_card_dvd_degree_mul_GL block P 2
    (affine_prime_dimension block P 4 2 2 hr hp (by norm_num))
  have hcard : Nat.card
      (Matrix.GeneralLinearGroup (Fin 2) (ZMod P.p)) = 6 := by
    rw [Matrix.card_GL_field, ZMod.card]
    norm_num [hp]
  simpa only [hr, hcard] using hdiv

/-- Every degree-eight primitive affine component has order dividing
`8 |GL₃(2)| = 1344`. -/
theorem component_card_dvd_1344
    (hr : Nat.card block.Fibre = 8) :
    Nat.card block.Component ∣ 1344 := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  let C := P.elementaryChart block.component_preprimitive
  letI : Fact P.p.Prime := C.primeFact
  letI : AddCommGroup C.V := C.addCommGroup
  letI : Module (ZMod P.p) C.V := C.module
  letI : FiniteDimensional (ZMod P.p) C.V := C.finiteDimensional
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v))
    C.equiv.symm.injective
  have hdegree0 : Nat.card block.Fibre = P.p ^ C.d := by
    simpa [PrimitiveAffineProfile.ElementaryChart.d] using
      P.degree_eq_prime_pow_finrank C.equiv
        ⟨basePoint, block.map_base⟩
  have hdegree : 8 = P.p ^ C.d := hr.symm.trans hdegree0
  have hpd := prime_pow_positive_injective (d := C.d) (e := 3)
    P.p_prime Nat.prime_two C.d_pos (by norm_num)
      (hdegree.symm.trans (by norm_num))
  have hp : P.p = 2 := hpd.1
  have hd : C.d = 3 := hpd.2
  have hdiv := component_card_dvd_degree_mul_GL block P 3
    (affine_prime_dimension block P 8 2 3 hr hp (by norm_num))
  have hcard : Nat.card
      (Matrix.GeneralLinearGroup (Fin 3) (ZMod P.p)) = 168 := by
    rw [Matrix.card_GL_field, ZMod.card]
    norm_num [hp]
    decide
  simpa only [hr, hcard] using hdiv

/-- Every degree-nine primitive affine component has order dividing
`9 |GL₂(3)| = 432`. -/
theorem component_card_dvd_432
    (hr : Nat.card block.Fibre = 9) :
    Nat.card block.Component ∣ 432 := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  let C := P.elementaryChart block.component_preprimitive
  letI : Fact P.p.Prime := C.primeFact
  letI : AddCommGroup C.V := C.addCommGroup
  letI : Module (ZMod P.p) C.V := C.module
  letI : FiniteDimensional (ZMod P.p) C.V := C.finiteDimensional
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v))
    C.equiv.symm.injective
  have hdegree0 : Nat.card block.Fibre = P.p ^ C.d := by
    simpa [PrimitiveAffineProfile.ElementaryChart.d] using
      P.degree_eq_prime_pow_finrank C.equiv
        ⟨basePoint, block.map_base⟩
  have hdegree : 9 = P.p ^ C.d := hr.symm.trans hdegree0
  have hpd := prime_pow_positive_injective (d := C.d) (e := 2)
    P.p_prime (by norm_num : Nat.Prime 3) C.d_pos (by norm_num)
      (hdegree.symm.trans (by norm_num))
  have hp : P.p = 3 := hpd.1
  have hd : C.d = 2 := hpd.2
  have hdiv := component_card_dvd_degree_mul_GL block P 2
    (affine_prime_dimension block P 9 3 2 hr hp (by norm_num))
  have hcard : Nat.card
      (Matrix.GeneralLinearGroup (Fin 2) (ZMod P.p)) = 48 := by
    rw [Matrix.card_GL_field, ZMod.card]
    norm_num [hp]
  simpa only [hr, hcard] using hdiv

/-- Every degree-sixteen primitive affine component has order dividing
`16 |GL₄(2)| = 322560`. -/
theorem component_card_dvd_322560
    (hr : Nat.card block.Fibre = 16) :
    Nat.card block.Component ∣ 322560 := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  let C := P.elementaryChart block.component_preprimitive
  letI : Fact P.p.Prime := C.primeFact
  letI : AddCommGroup C.V := C.addCommGroup
  letI : Module (ZMod P.p) C.V := C.module
  letI : FiniteDimensional (ZMod P.p) C.V := C.finiteDimensional
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v))
    C.equiv.symm.injective
  have hdegree0 : Nat.card block.Fibre = P.p ^ C.d := by
    simpa [PrimitiveAffineProfile.ElementaryChart.d] using
      P.degree_eq_prime_pow_finrank C.equiv
        ⟨basePoint, block.map_base⟩
  have hdegree : 16 = P.p ^ C.d := hr.symm.trans hdegree0
  have hpd := prime_pow_positive_injective (d := C.d) (e := 4)
    P.p_prime Nat.prime_two C.d_pos (by norm_num)
      (hdegree.symm.trans (by norm_num))
  have hp : P.p = 2 := hpd.1
  have hd : C.d = 4 := hpd.2
  have hdiv := component_card_dvd_degree_mul_GL block P 4
    (affine_prime_dimension block P 16 2 4 hr hp (by norm_num))
  have hcard : Nat.card
      (Matrix.GeneralLinearGroup (Fin 4) (ZMod P.p)) = 20160 := by
    rw [Matrix.card_GL_field, ZMod.card]
    norm_num [hp]
    decide
  simpa only [hr, hcard] using hdiv

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
