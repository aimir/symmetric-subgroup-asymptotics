import SymmetricSubgroupAsymptotics.GLThreeThreeSolubleIrreducibleOrderBound
import SymmetricSubgroupAsymptotics.PrimitiveAffineTwentySevenLinearEmbedding
import SymmetricSubgroupAsymptotics.PrimitiveAffineBottomFibre

/-! The actual soluble degree27 affine complement has order at most78,
without any primitive catalogue correspondence. The original complement
acts faithfully and irreducibly on its actual three-dimensional ternary
translation module. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu

variable {G : Type} [Group G] [Finite G] [MulAction G (Fin 27)]
    [FaithfulSMul G (Fin 27)]

theorem primitiveAffineTwentySeven_soluble_card_le_without_catalogue
    (P : PrimitiveAffineProfile G (Fin 27))
    (hprimitive : MulAction.IsPreprimitive G (Fin 27)) (x : Fin 27)
    (hsoluble : IsSolvable (P.complement x)) : Nat.card (P.complement x)≤78 := by
  let C := P.elementaryChart hprimitive
  letI : Fact P.p.Prime := C.primeFact
  letI : AddCommGroup C.V := C.addCommGroup
  letI : Module (ZMod P.p) C.V := C.module
  letI : FiniteDimensional (ZMod P.p) C.V := C.finiteDimensional
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v)) C.equiv.symm.injective
  letI : IsSolvable (P.complement x) := hsoluble
  let rho := (P.complementRepresentation hprimitive C x).ρ
  have hf : Function.Injective rho :=
    P.complementRepresentationCore_injective hprimitive C x
  have hirr : Representation.IsIrreducible rho :=
    P.complementRepresentation_irreducible hprimitive C x
  have hpd := P.degreeTwentySeven_prime_dimension hprimitive x
  have hdim : Module.finrank (ZMod P.p) C.V=3 := by
    simpa only [PrimitiveAffineProfile.ElementaryChart.d] using hpd.2
  exact GLThreeThreeSolubleIrreducibleOrderBound.card_le_of_prime_eq_three
    hpd.1 rho hf hirr hdim

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
