import SymmetricSubgroupAsymptotics.PrimitiveAffineSolubleDerivedTarget
import SymmetricSubgroupAsymptotics.ElementaryQuotientRepresentation

/-!
# The faithful affine-complement representation

This isolates the small part of the bottom-fibre development needed by the
finite primitive-affine structural models: conjugation by the literal point
stabilizer on an elementary translation chart is a faithful linear
representation.  The separate name avoids colliding with the richer
bottom-fibre API when both files are imported downstream.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineProfile

variable {L Omega : Type} [Group L] [Finite L] [MulAction L Omega]
  [Finite Omega] [Nontrivial Omega] [FaithfulSMul L Omega]
  (P : PrimitiveAffineProfile L Omega)

theorem complementActionCore_preserves_equiv_ker
    (hprimitive : MulAction.IsPreprimitive L Omega)
    (C : P.ElementaryChart hprimitive) (x : Omega)
    (h : P.complement x) (v : P.V) (hv : C.equiv v = 1) :
    C.equiv (P.complementAction x h v) = 1 := by
  have hv1 : v = 1 := by
    apply C.equiv.injective
    rw [hv, map_one]
  rw [hv1, map_one, map_one]

abbrev complementRepresentationCore
    (hprimitive : MulAction.IsPreprimitive L Omega)
    (C : P.ElementaryChart hprimitive) (x : Omega) :
    Rep (ZMod P.p) (P.complement x) := by
  letI : Fact P.p.Prime := C.primeFact
  exact Rep.of (elementaryQuotientRepresentation (p := P.p)
    (R := P.V) (V := C.V)
    (P.complementAction x) C.equiv.toMonoidHom C.equiv.surjective
      (P.complementActionCore_preserves_equiv_ker hprimitive C x))

theorem complementRepresentationCore_apply
    (hprimitive : MulAction.IsPreprimitive L Omega)
    (C : P.ElementaryChart hprimitive) (x : Omega)
    (h : P.complement x) (v : C.V) :
    (P.complementRepresentationCore hprimitive C x).ρ h v =
      (C.equiv (P.complementAction x h
        (C.equiv.symm (Multiplicative.ofAdd v)))).toAdd := by
  letI : Fact P.p.Prime := C.primeFact
  change (elementaryQuotientRepresentation (p := P.p)
    (R := P.V) (V := C.V)
    (P.complementAction x) C.equiv.toMonoidHom C.equiv.surjective
      (P.complementActionCore_preserves_equiv_ker hprimitive C x)) h v = _
  symm
  have he := elementaryQuotientRepresentation_equivariant (p := P.p)
      (P.complementAction x) C.equiv.toMonoidHom C.equiv.surjective
      (P.complementActionCore_preserves_equiv_ker hprimitive C x) h
      (C.equiv.symm (Multiplicative.ofAdd v))
  convert he using 1
  · simp

theorem complementRepresentationCore_injective
    (hprimitive : MulAction.IsPreprimitive L Omega)
    (C : P.ElementaryChart hprimitive) (x : Omega) :
    letI : Fact P.p.Prime := C.primeFact
    Function.Injective (P.complementRepresentationCore hprimitive C x).ρ := by
  letI : Fact P.p.Prime := C.primeFact
  rw [injective_iff_map_eq_one]
  intro h hh
  apply P.complementAction_injective x
  apply MulEquiv.ext
  intro v
  apply C.equiv.injective
  apply Multiplicative.toAdd.injective
  have hz := DFunLike.congr_fun hh (C.equiv v).toAdd
  rw [P.complementRepresentationCore_apply] at hz
  simpa using hz

end PrimitiveAffineProfile
end SymmetricSubgroupAsymptotics
