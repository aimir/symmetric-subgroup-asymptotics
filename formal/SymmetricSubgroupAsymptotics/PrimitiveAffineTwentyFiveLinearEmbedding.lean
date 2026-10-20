import SymmetricSubgroupAsymptotics.PrimitiveAffineComplementRepresentationCore
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-! The literal degree25 affine complement embeds faithfully in GL2(5).
The prime and dimension are derived from the actual translation-module
cardinal, not supplied as a degree-specific linear/composition datum. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineProfile

local instance twentyFiveLinearEmbeddingPrimeFact : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

private theorem twentyFive_primePower_unique
    {p q d e : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hd : 0 < d) (he : 0 < e) (h : p^d=q^e) : p=q ∧ d=e := by
  have hpdiv : p ∣ q := hp.dvd_of_dvd_pow (by
    rw [←h]
    exact dvd_pow_self p hd.ne')
  have hqdiv : q ∣ p := hq.dvd_of_dvd_pow (by
    rw [h]
    exact dvd_pow_self q he.ne')
  have hpq : p=q := Nat.dvd_antisymm hpdiv hqdiv
  subst q
  exact ⟨rfl,Nat.pow_right_injective hp.two_le h⟩

variable {L : Type} [Group L] [MulAction L (Fin 25)] [Finite L]
  [FaithfulSMul L (Fin 25)]

theorem degreeTwentyFive_prime_dimension
    (P : PrimitiveAffineProfile L (Fin 25))
    (hprimitive : MulAction.IsPreprimitive L (Fin 25)) (x : Fin 25) :
    P.p=5 ∧ (P.elementaryChart hprimitive).d=2 := by
  let C := P.elementaryChart hprimitive
  letI : Fact P.p.Prime := C.primeFact
  letI : AddCommGroup C.V := C.addCommGroup
  letI : Module (ZMod P.p) C.V := C.module
  letI : FiniteDimensional (ZMod P.p) C.V := C.finiteDimensional
  letI : Nontrivial C.V := C.nontrivial
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v)) C.equiv.symm.injective
  have hdegree : P.p^C.d=5^2 := by
    have hcard : Nat.card (Fin 25)=P.p^Module.finrank (ZMod P.p) C.V := by
      calc
        Nat.card (Fin 25)=Nat.card P.V := (P.card_eq x).symm
        _=Nat.card C.V := Nat.card_congr C.equiv.toEquiv
        _=P.p^Module.finrank (ZMod P.p) C.V := by
          rw [Module.natCard_eq_pow_finrank (K := ZMod P.p) (V := C.V),Nat.card_zmod]
    simpa [PrimitiveAffineProfile.ElementaryChart.d] using hcard.symm
  exact twentyFive_primePower_unique P.p_prime (by norm_num : Nat.Prime 5)
    C.d_pos (by norm_num) hdegree

/-- The matrix map is induced by the SAME actual complement representation. -/
theorem exists_complementLinearEmbedding_degreeTwentyFive
    (P : PrimitiveAffineProfile L (Fin 25))
    (hprimitive : MulAction.IsPreprimitive L (Fin 25)) (x : Fin 25) :
    ∃ phi : P.complement x →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 5),
      Function.Injective phi := by
  let C := P.elementaryChart hprimitive
  letI : Fact P.p.Prime := C.primeFact
  letI : AddCommGroup C.V := C.addCommGroup
  letI : Module (ZMod P.p) C.V := C.module
  letI : FiniteDimensional (ZMod P.p) C.V := C.finiteDimensional
  have hp_hd := P.degreeTwentyFive_prime_dimension hprimitive x
  have hp : P.p=5 := hp_hd.1
  have hfin : Module.finrank (ZMod P.p) C.V=2 := by
    simpa [C,PrimitiveAffineProfile.ElementaryChart.d] using hp_hd.2
  let basis : Module.Basis (Fin 2) (ZMod P.p) C.V :=
    Module.finBasisOfFinrankEq (ZMod P.p) C.V hfin
  let rho := (P.complementRepresentationCore hprimitive C x).ρ
  let phi0 : P.complement x →* Matrix.GeneralLinearGroup (Fin 2) (ZMod P.p) :=
    (Matrix.GeneralLinearGroup.toLin' basis).symm.toMonoidHom.comp
      (Representation.asGroupHom rho)
  have hphi0 : Function.Injective phi0 := by
    intro a b hab
    apply P.complementRepresentationCore_injective hprimitive C x
    have hab' : Representation.asGroupHom rho a=Representation.asGroupHom rho b := by
      exact (Matrix.GeneralLinearGroup.toLin' basis).symm.injective (by
        simpa [phi0] using hab)
    exact congrArg Units.val hab'
  let e : ZMod P.p ≃+* ZMod 5 := ZMod.ringEquivCongr hp
  let phi : P.complement x →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 5) :=
    (Matrix.GeneralLinearGroup.map e.toRingHom).comp phi0
  refine ⟨phi,?_⟩
  intro a b hab
  apply hphi0
  apply Units.ext
  ext i j
  apply e.injective
  have hij := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 2) (ZMod 5) => g i j) hab
  simpa [phi] using hij

noncomputable def complementLinearMap_degreeTwentyFive
    (P : PrimitiveAffineProfile L (Fin 25))
    (hprimitive : MulAction.IsPreprimitive L (Fin 25)) (x : Fin 25) :
    P.complement x →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 5) :=
  Classical.choose (P.exists_complementLinearEmbedding_degreeTwentyFive hprimitive x)

theorem complementLinearMap_degreeTwentyFive_injective
    (P : PrimitiveAffineProfile L (Fin 25))
    (hprimitive : MulAction.IsPreprimitive L (Fin 25)) (x : Fin 25) :
    Function.Injective (P.complementLinearMap_degreeTwentyFive hprimitive x) :=
  Classical.choose_spec (P.exists_complementLinearEmbedding_degreeTwentyFive hprimitive x)

theorem glTwoFive_card : Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 5))=480 := by
  rw [Matrix.card_GL_field]
  norm_num [Fin.prod_univ_two]

theorem complement_card_dvd_480_degreeTwentyFive
    (P : PrimitiveAffineProfile L (Fin 25))
    (hprimitive : MulAction.IsPreprimitive L (Fin 25)) (x : Fin 25) :
    Nat.card (P.complement x) ∣ 480 := by
  rw [←glTwoFive_card]
  exact Subgroup.card_dvd_of_injective (P.complementLinearMap_degreeTwentyFive hprimitive x)
    (P.complementLinearMap_degreeTwentyFive_injective hprimitive x)

end SymmetricSubgroupAsymptotics.PrimitiveAffineProfile
