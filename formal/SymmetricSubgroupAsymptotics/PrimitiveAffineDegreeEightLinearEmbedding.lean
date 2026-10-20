import SymmetricSubgroupAsymptotics.PrimitiveAffineComplementRepresentationCore
import SymmetricSubgroupAsymptotics.StandardThreeDimensionalLinearGroups

/-! The literal stabilizer of a faithful primitive affine action of degree
eight embeds in the actual GL(3,2). The profile prime and dimension are
derived from the translation cardinal, not supplied as catalogue facts. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineProfile

private theorem degreeEight_primePower_unique
    {p q d e : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hd : 0 < d) (he : 0 < e) (h : p ^ d = q ^ e) : p = q ∧ d = e := by
  have hpdiv : p ∣ q := hp.dvd_of_dvd_pow (by
    rw [← h]
    exact dvd_pow_self p hd.ne')
  have hqdiv : q ∣ p := hq.dvd_of_dvd_pow (by
    rw [h]
    exact dvd_pow_self q he.ne')
  have hpq : p = q := Nat.dvd_antisymm hpdiv hqdiv
  subst q
  exact ⟨rfl, Nat.pow_right_injective hp.two_le h⟩

variable {L Ω : Type} [Group L] [MulAction L Ω] [Finite L]
  [Finite Ω] [Nontrivial Ω] [FaithfulSMul L Ω]

theorem degreeEight_prime_dimension (P : PrimitiveAffineProfile L Ω)
    (hprimitive : MulAction.IsPreprimitive L Ω) (x : Ω) (hdegree : Nat.card Ω = 8) :
    P.p = 2 ∧ (P.elementaryChart hprimitive).d = 3 := by
  let C := P.elementaryChart hprimitive
  letI : Fact P.p.Prime := C.primeFact
  letI : AddCommGroup C.V := C.addCommGroup
  letI : Module (ZMod P.p) C.V := C.module
  letI : FiniteDimensional (ZMod P.p) C.V := C.finiteDimensional
  letI : Nontrivial C.V := C.nontrivial
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v)) C.equiv.symm.injective
  have hcard : Nat.card Ω = P.p ^ Module.finrank (ZMod P.p) C.V := by
    calc
      Nat.card Ω = Nat.card P.V := (P.card_eq x).symm
      _ = Nat.card C.V := Nat.card_congr C.equiv.toEquiv
      _ = P.p ^ Module.finrank (ZMod P.p) C.V := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod P.p) (V := C.V), Nat.card_zmod]
  have hpower : P.p ^ C.d = 2 ^ 3 := by
    simpa [PrimitiveAffineProfile.ElementaryChart.d, hdegree] using hcard.symm
  exact degreeEight_primePower_unique P.p_prime (by norm_num : Nat.Prime 2)
    C.d_pos (by norm_num) hpower

/-- The matrix homomorphism is constructed from the actual conjugation
representation on the actual elementary translation chart. -/
theorem exists_complementLinearEmbedding_degreeEight
    (P : PrimitiveAffineProfile L Ω) (hprimitive : MulAction.IsPreprimitive L Ω)
    (x : Ω) (hdegree : Nat.card Ω = 8) :
    ∃ phi : P.complement x →*
        StandardThreeDimensionalLinearGroups.GeneralThree 2,
      Function.Injective phi := by
  let C := P.elementaryChart hprimitive
  letI : Fact P.p.Prime := C.primeFact
  letI : AddCommGroup C.V := C.addCommGroup
  letI : Module (ZMod P.p) C.V := C.module
  letI : FiniteDimensional (ZMod P.p) C.V := C.finiteDimensional
  have hp_hd := P.degreeEight_prime_dimension hprimitive x hdegree
  have hp : P.p = 2 := hp_hd.1
  have hfin : Module.finrank (ZMod P.p) C.V = 3 := by
    simpa [C, PrimitiveAffineProfile.ElementaryChart.d] using hp_hd.2
  let basis : Module.Basis (Fin 3) (ZMod P.p) C.V :=
    Module.finBasisOfFinrankEq (ZMod P.p) C.V hfin
  let rho := (P.complementRepresentationCore hprimitive C x).ρ
  let phi0 : P.complement x →* Matrix.GeneralLinearGroup (Fin 3) (ZMod P.p) :=
    (Matrix.GeneralLinearGroup.toLin' basis).symm.toMonoidHom.comp
      (Representation.asGroupHom rho)
  have hphi0 : Function.Injective phi0 := by
    intro a b hab
    apply P.complementRepresentationCore_injective hprimitive C x
    have hab' : Representation.asGroupHom rho a = Representation.asGroupHom rho b := by
      exact (Matrix.GeneralLinearGroup.toLin' basis).symm.injective (by
        simpa [phi0] using hab)
    exact congrArg Units.val hab'
  let e : ZMod P.p ≃+* ZMod 2 := ZMod.ringEquivCongr hp
  let phi : P.complement x →* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) :=
    (Matrix.GeneralLinearGroup.map e.toRingHom).comp phi0
  refine ⟨phi, ?_⟩
  intro a b hab
  apply hphi0
  apply Units.ext
  ext i j
  apply e.injective
  have hij := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) => g i j) hab
  simpa [phi] using hij

noncomputable def complementLinearMap_degreeEight
    (P : PrimitiveAffineProfile L Ω) (hprimitive : MulAction.IsPreprimitive L Ω)
    (x : Ω) (hdegree : Nat.card Ω = 8) :
    P.complement x →* StandardThreeDimensionalLinearGroups.GeneralThree 2 :=
  Classical.choose (P.exists_complementLinearEmbedding_degreeEight hprimitive x hdegree)

theorem complementLinearMap_degreeEight_injective
    (P : PrimitiveAffineProfile L Ω) (hprimitive : MulAction.IsPreprimitive L Ω)
    (x : Ω) (hdegree : Nat.card Ω = 8) :
    Function.Injective (P.complementLinearMap_degreeEight hprimitive x hdegree) :=
  Classical.choose_spec (P.exists_complementLinearEmbedding_degreeEight hprimitive x hdegree)

end SymmetricSubgroupAsymptotics.PrimitiveAffineProfile

end
