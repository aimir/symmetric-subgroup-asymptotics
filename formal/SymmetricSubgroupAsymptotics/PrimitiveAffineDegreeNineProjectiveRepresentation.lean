import SymmetricSubgroupAsymptotics.PrimitiveAffineComplementRepresentationCore
import SymmetricSubgroupAsymptotics.LinearThreeProjectiveCore

/-!
# The degree-nine primitive-affine projective representation

The point stabilizer of a primitive affine group of degree nine acts
faithfully on its translation module `F3^2`.  We transport that action to
`GL2(3)`, then use the literal projective action on four points.  Its kernel
is central of order two.  The projective image and its product with `C2`
therefore give the two distinct axes required by
the central-product construction, without importing its counting layer.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineProfile

private abbrev C2 := Multiplicative (ZMod 2)

private theorem primePowerPresentation_unique
    {p q d e : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hd : 0 < d) (he : 0 < e) (h : p ^ d = q ^ e) :
    p = q ∧ d = e := by
  have hpdiv : p ∣ q := hp.dvd_of_dvd_pow (by
    rw [← h]
    exact dvd_pow_self p hd.ne')
  have hqdiv : q ∣ p := hq.dvd_of_dvd_pow (by
    rw [h]
    exact dvd_pow_self q he.ne')
  have hpq : p = q := Nat.dvd_antisymm hpdiv hqdiv
  subst q
  exact ⟨rfl, Nat.pow_right_injective hp.two_le h⟩

variable {L : Type} [Group L] [MulAction L (Fin 9)] [Finite L]
  [FaithfulSMul L (Fin 9)]

/-! ## The faithful matrix and projective maps -/

/-- The literal degree-nine complement embeds in `GL2(3)`. -/
theorem exists_complementLinearEmbedding_degreeNine
    (P : PrimitiveAffineProfile L (Fin 9))
    (hprimitive : MulAction.IsPreprimitive L (Fin 9)) (x : Fin 9) :
    ∃ phi : P.complement x →* LinearThreeCore.GL3, Function.Injective phi := by
  let C := P.elementaryChart hprimitive
  letI : Fact P.p.Prime := C.primeFact
  letI : AddCommGroup C.V := C.addCommGroup
  letI : Module (ZMod P.p) C.V := C.module
  letI : FiniteDimensional (ZMod P.p) C.V := C.finiteDimensional
  letI : Nontrivial C.V := C.nontrivial
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v))
    C.equiv.symm.injective
  have hdegree : P.p ^ C.d = 3 ^ 2 := by
    have hcard : Nat.card (Fin 9) =
        P.p ^ Module.finrank (ZMod P.p) C.V := by
      calc
        Nat.card (Fin 9) = Nat.card P.V := (P.card_eq x).symm
        _ = Nat.card C.V := Nat.card_congr C.equiv.toEquiv
        _ = P.p ^ Module.finrank (ZMod P.p) C.V := by
          rw [Module.natCard_eq_pow_finrank (K := ZMod P.p) (V := C.V),
            Nat.card_zmod]
    simpa [PrimitiveAffineProfile.ElementaryChart.d] using hcard.symm
  have hp_hd := primePowerPresentation_unique P.p_prime
    (by norm_num : Nat.Prime 3) C.d_pos (by norm_num) hdegree
  have hp : P.p = 3 := hp_hd.1
  have hd : C.d = 2 := hp_hd.2
  have hfin : Module.finrank (ZMod P.p) C.V = 2 := by
    simpa [PrimitiveAffineProfile.ElementaryChart.d] using hd
  let basis : Module.Basis (Fin 2) (ZMod P.p) C.V :=
    Module.finBasisOfFinrankEq (ZMod P.p) C.V hfin
  let rho := (P.complementRepresentationCore hprimitive C x).ρ
  let phi0 : P.complement x →*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod P.p) :=
    (Matrix.GeneralLinearGroup.toLin' basis).symm.toMonoidHom.comp
      (Representation.asGroupHom rho)
  have hphi0 : Function.Injective phi0 := by
    intro a b hab
    apply P.complementRepresentationCore_injective hprimitive C x
    have hab' : Representation.asGroupHom rho a =
        Representation.asGroupHom rho b := by
      exact (Matrix.GeneralLinearGroup.toLin' basis).symm.injective (by
        simpa [phi0] using hab)
    exact congrArg Units.val hab'
  let e : ZMod P.p ≃+* ZMod 3 := ZMod.ringEquivCongr hp
  let phi : P.complement x →* LinearThreeCore.GL3 :=
    (Matrix.GeneralLinearGroup.map e.toRingHom).comp phi0
  refine ⟨phi, ?_⟩
  intro a b hab
  apply hphi0
  apply Units.ext
  ext i j
  apply e.injective
  have hij := congrArg (fun g : LinearThreeCore.GL3 => g i j) hab
  simpa [phi] using hij

/-- A chosen faithful matrix realization of the complement. -/
noncomputable def complementLinearMap_degreeNine
    (P : PrimitiveAffineProfile L (Fin 9))
    (hprimitive : MulAction.IsPreprimitive L (Fin 9)) (x : Fin 9) :
    P.complement x →* LinearThreeCore.GL3 :=
  Classical.choose (P.exists_complementLinearEmbedding_degreeNine hprimitive x)

theorem complementLinearMap_degreeNine_injective
    (P : PrimitiveAffineProfile L (Fin 9))
    (hprimitive : MulAction.IsPreprimitive L (Fin 9)) (x : Fin 9) :
    Function.Injective (P.complementLinearMap_degreeNine hprimitive x) :=
  Classical.choose_spec (P.exists_complementLinearEmbedding_degreeNine hprimitive x)

/-- The four-point projective action of the degree-nine complement. -/
def complementProjectiveMap_degreeNine
    (P : PrimitiveAffineProfile L (Fin 9))
    (hprimitive : MulAction.IsPreprimitive L (Fin 9)) (x : Fin 9) :
    P.complement x →* Equiv.Perm (Fin 4) :=
  LinearThreeCore.projective.comp (P.complementLinearMap_degreeNine hprimitive x)

/-- Its literal projective image. -/
abbrev DegreeNineProjectiveImage
    (P : PrimitiveAffineProfile L (Fin 9))
    (hprimitive : MulAction.IsPreprimitive L (Fin 9)) (x : Fin 9) :=
  (P.complementProjectiveMap_degreeNine hprimitive x).range

/-- The projective map with its codomain restricted to the actual image. -/
def complementProjectiveRangeMap_degreeNine
    (P : PrimitiveAffineProfile L (Fin 9))
    (hprimitive : MulAction.IsPreprimitive L (Fin 9)) (x : Fin 9) :
    P.complement x →* P.DegreeNineProjectiveImage hprimitive x :=
  (P.complementProjectiveMap_degreeNine hprimitive x).rangeRestrict

theorem complementProjectiveRangeMap_degreeNine_surjective
    (P : PrimitiveAffineProfile L (Fin 9))
    (hprimitive : MulAction.IsPreprimitive L (Fin 9)) (x : Fin 9) :
    Function.Surjective (P.complementProjectiveRangeMap_degreeNine hprimitive x) :=
  (P.complementProjectiveMap_degreeNine hprimitive x).rangeRestrict_surjective

theorem complementProjectiveRangeMap_degreeNine_central_kernel
    (P : PrimitiveAffineProfile L (Fin 9))
    (hprimitive : MulAction.IsPreprimitive L (Fin 9)) (x : Fin 9) :
    ∀ z ∈ (P.complementProjectiveRangeMap_degreeNine hprimitive x).ker,
      ∀ g : P.complement x, z * g = g * z := by
  intro z hz g
  apply P.complementLinearMap_degreeNine_injective hprimitive x
  simp only [map_mul]
  apply LinearThreeCore.central_of_ker
  rw [MonoidHom.mem_ker] at hz ⊢
  exact congrArg Subtype.val hz

/-- The projective kernel embeds in the binary kernel of `GL2(3)`. -/
def complementProjectiveKernelEmbedding_degreeNine
    (P : PrimitiveAffineProfile L (Fin 9))
    (hprimitive : MulAction.IsPreprimitive L (Fin 9)) (x : Fin 9) :
    (P.complementProjectiveRangeMap_degreeNine hprimitive x).ker →*
      LinearThreeCore.projective.ker where
  toFun z := ⟨P.complementLinearMap_degreeNine hprimitive x z.1, by
    have hz := z.2
    rw [MonoidHom.mem_ker] at hz ⊢
    exact congrArg Subtype.val hz⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by apply Subtype.ext; simp

theorem complementProjectiveKernelEmbedding_degreeNine_injective
    (P : PrimitiveAffineProfile L (Fin 9))
    (hprimitive : MulAction.IsPreprimitive L (Fin 9)) (x : Fin 9) :
    Function.Injective (P.complementProjectiveKernelEmbedding_degreeNine hprimitive x) := by
  intro a b hab
  apply Subtype.ext
  apply P.complementLinearMap_degreeNine_injective hprimitive x
  exact congrArg Subtype.val hab

theorem complementProjectiveKernel_card_le_two_degreeNine
    (P : PrimitiveAffineProfile L (Fin 9))
    (hprimitive : MulAction.IsPreprimitive L (Fin 9)) (x : Fin 9) :
    Nat.card (P.complementProjectiveRangeMap_degreeNine hprimitive x).ker ≤ 2 := by
  calc
    Nat.card (P.complementProjectiveRangeMap_degreeNine hprimitive x).ker ≤
        Nat.card LinearThreeCore.projective.ker :=
      Nat.card_le_card_of_injective
        (P.complementProjectiveKernelEmbedding_degreeNine hprimitive x)
        (P.complementProjectiveKernelEmbedding_degreeNine_injective hprimitive x)
    _ ≤ 2 := LinearThreeCore.card_ker_projective_le_two

end PrimitiveAffineProfile
end SymmetricSubgroupAsymptotics
