import SymmetricSubgroupAsymptotics.LinearThreeSolvable
import SymmetricSubgroupAsymptotics.PrimitiveAffineBottomFibre
import SymmetricSubgroupAsymptotics.PrimitiveAffineMediumOddSource

/-!
# Solvability of the degree-nine affine complement

A primitive affine group of degree nine has translation module
`F₃²`.  Its literal point stabilizer acts faithfully on that module, so it
embeds in `GL₂(3)`.  The preceding projective calculation proves that the
latter group is soluble.  Thus the degree-nine solvability field formerly
carried by the finite catalogue is a theorem.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- A spelling of `GL₂(3)` that permits the characteristic to be recovered
from a structural affine profile before the representation is transported
to matrices. -/
theorem glFinTwoZMod_isSolvable {p : ℕ} (hp : p = 3) :
    IsSolvable (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) := by
  subst p
  exact LinearThree.gl3_isSolvable

namespace PrimitiveAffineProfile

variable {L : Type} [Group L] [MulAction L (Fin 9)] [Finite L]
  [FaithfulSMul L (Fin 9)]

/-- The point stabilizer of a primitive affine group of degree nine is
soluble. -/
theorem complement_isSolvable_degreeNine
    (P : PrimitiveAffineProfile L (Fin 9))
    (hprimitive : MulAction.IsPreprimitive L (Fin 9)) (x : Fin 9) :
    IsSolvable (P.complement x) := by
  let C := P.elementaryChart hprimitive
  letI : Fact P.p.Prime := C.primeFact
  letI : AddCommGroup C.V := C.addCommGroup
  letI : Module (ZMod P.p) C.V := C.module
  letI : FiniteDimensional (ZMod P.p) C.V := C.finiteDimensional
  letI : Nontrivial C.V := C.nontrivial
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v))
    C.equiv.symm.injective
  have hd : C.d = 2 := C.dimension_eq_of_degree_eq_prime_pow P x
    (by norm_num : Nat.Prime 3) (by norm_num) (by norm_num)
  have hp : P.p = 3 := by
    have hdegree : 9 = P.p ^ C.d := by
      simpa [PrimitiveAffineProfile.ElementaryChart.d] using
        P.degree_eq_prime_pow_finrank C.equiv x
    rw [hd] at hdegree
    nlinarith [P.p_prime.two_le]
  have hfin : Module.finrank (ZMod P.p) C.V = 2 := by
    simpa [PrimitiveAffineProfile.ElementaryChart.d] using hd
  let basis : Module.Basis (Fin 2) (ZMod P.p) C.V :=
    Module.finBasisOfFinrankEq (ZMod P.p) C.V hfin
  let rho := (P.complementRepresentation hprimitive C x).ρ
  let phi : P.complement x →*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod P.p) :=
    (Matrix.GeneralLinearGroup.toLin' basis).symm.toMonoidHom.comp
      (Representation.asGroupHom rho)
  letI : IsSolvable
      (Matrix.GeneralLinearGroup (Fin 2) (ZMod P.p)) :=
    glFinTwoZMod_isSolvable hp
  apply solvable_of_solvable_injective (f := phi)
  intro a b hab
  apply P.complementRepresentation_injective hprimitive C x
  have hab' : Representation.asGroupHom rho a =
      Representation.asGroupHom rho b := by
    exact (Matrix.GeneralLinearGroup.toLin' basis).symm.injective (by
      simpa [phi] using hab)
  exact congrArg Units.val hab'

end PrimitiveAffineProfile
end SymmetricSubgroupAsymptotics

end
