import SymmetricSubgroupAsymptotics.PrimitiveAffineComplementRepresentationCore
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-! The literal degree27 affine complement embeds faithfully in GL3(3).
The prime and dimension are derived from the actual translation-module
cardinal, not supplied as a degree-specific linear/composition datum. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineProfile

local instance twentySevenLinearEmbeddingPrimeFact : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

private theorem twentySeven_primePower_unique
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

variable {L : Type} [Group L] [MulAction L (Fin 27)] [Finite L]
  [FaithfulSMul L (Fin 27)]

theorem degreeTwentySeven_prime_dimension
    (P : PrimitiveAffineProfile L (Fin 27))
    (hprimitive : MulAction.IsPreprimitive L (Fin 27)) (x : Fin 27) :
    P.p=3 ∧ (P.elementaryChart hprimitive).d=3 := by
  let C := P.elementaryChart hprimitive
  letI : Fact P.p.Prime := C.primeFact
  letI : AddCommGroup C.V := C.addCommGroup
  letI : Module (ZMod P.p) C.V := C.module
  letI : FiniteDimensional (ZMod P.p) C.V := C.finiteDimensional
  letI : Nontrivial C.V := C.nontrivial
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v)) C.equiv.symm.injective
  have hdegree : P.p^C.d=3^3 := by
    have hcard : Nat.card (Fin 27)=P.p^Module.finrank (ZMod P.p) C.V := by
      calc
        Nat.card (Fin 27)=Nat.card P.V := (P.card_eq x).symm
        _=Nat.card C.V := Nat.card_congr C.equiv.toEquiv
        _=P.p^Module.finrank (ZMod P.p) C.V := by
          rw [Module.natCard_eq_pow_finrank (K := ZMod P.p) (V := C.V),Nat.card_zmod]
    simpa [PrimitiveAffineProfile.ElementaryChart.d] using hcard.symm
  exact twentySeven_primePower_unique P.p_prime (by norm_num : Nat.Prime 3)
    C.d_pos (by norm_num) hdegree

/-- The matrix map is induced by the SAME actual complement representation. -/
theorem exists_complementLinearEmbedding_degreeTwentySeven
    (P : PrimitiveAffineProfile L (Fin 27))
    (hprimitive : MulAction.IsPreprimitive L (Fin 27)) (x : Fin 27) :
    ∃ phi : P.complement x →* Matrix.GeneralLinearGroup (Fin 3) (ZMod 3),
      Function.Injective phi := by
  let C := P.elementaryChart hprimitive
  letI : Fact P.p.Prime := C.primeFact
  letI : AddCommGroup C.V := C.addCommGroup
  letI : Module (ZMod P.p) C.V := C.module
  letI : FiniteDimensional (ZMod P.p) C.V := C.finiteDimensional
  have hp_hd := P.degreeTwentySeven_prime_dimension hprimitive x
  have hp : P.p=3 := hp_hd.1
  have hfin : Module.finrank (ZMod P.p) C.V=3 := by
    simpa [C,PrimitiveAffineProfile.ElementaryChart.d] using hp_hd.2
  let basis : Module.Basis (Fin 3) (ZMod P.p) C.V :=
    Module.finBasisOfFinrankEq (ZMod P.p) C.V hfin
  let rho := (P.complementRepresentationCore hprimitive C x).ρ
  let phi0 : P.complement x →* Matrix.GeneralLinearGroup (Fin 3) (ZMod P.p) :=
    (Matrix.GeneralLinearGroup.toLin' basis).symm.toMonoidHom.comp
      (Representation.asGroupHom rho)
  have hphi0 : Function.Injective phi0 := by
    intro a b hab
    apply P.complementRepresentationCore_injective hprimitive C x
    have hab' : Representation.asGroupHom rho a=Representation.asGroupHom rho b := by
      exact (Matrix.GeneralLinearGroup.toLin' basis).symm.injective (by
        simpa [phi0] using hab)
    exact congrArg Units.val hab'
  let e : ZMod P.p ≃+* ZMod 3 := ZMod.ringEquivCongr hp
  let phi : P.complement x →* Matrix.GeneralLinearGroup (Fin 3) (ZMod 3) :=
    (Matrix.GeneralLinearGroup.map e.toRingHom).comp phi0
  refine ⟨phi,?_⟩
  intro a b hab
  apply hphi0
  apply Units.ext
  ext i j
  apply e.injective
  have hij := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 3) (ZMod 3) => g i j) hab
  simpa [phi] using hij

noncomputable def complementLinearMap_degreeTwentySeven
    (P : PrimitiveAffineProfile L (Fin 27))
    (hprimitive : MulAction.IsPreprimitive L (Fin 27)) (x : Fin 27) :
    P.complement x →* Matrix.GeneralLinearGroup (Fin 3) (ZMod 3) :=
  Classical.choose (P.exists_complementLinearEmbedding_degreeTwentySeven hprimitive x)

theorem complementLinearMap_degreeTwentySeven_injective
    (P : PrimitiveAffineProfile L (Fin 27))
    (hprimitive : MulAction.IsPreprimitive L (Fin 27)) (x : Fin 27) :
    Function.Injective (P.complementLinearMap_degreeTwentySeven hprimitive x) :=
  Classical.choose_spec (P.exists_complementLinearEmbedding_degreeTwentySeven hprimitive x)

theorem glThreeThree_card : Nat.card (Matrix.GeneralLinearGroup (Fin 3) (ZMod 3))=11232 := by
  rw [Matrix.card_GL_field]
  norm_num [Fin.prod_univ_succ]

theorem complement_card_dvd_11232_degreeTwentySeven
    (P : PrimitiveAffineProfile L (Fin 27))
    (hprimitive : MulAction.IsPreprimitive L (Fin 27)) (x : Fin 27) :
    Nat.card (P.complement x) ∣ 11232 := by
  rw [←glThreeThree_card]
  exact Subgroup.card_dvd_of_injective (P.complementLinearMap_degreeTwentySeven hprimitive x)
    (P.complementLinearMap_degreeTwentySeven_injective hprimitive x)

end SymmetricSubgroupAsymptotics.PrimitiveAffineProfile
