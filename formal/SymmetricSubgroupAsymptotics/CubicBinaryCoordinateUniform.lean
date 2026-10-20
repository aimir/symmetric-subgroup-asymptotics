import SymmetricSubgroupAsymptotics.CubicBinaryQuotientCoordinates
import SymmetricSubgroupAsymptotics.PermutationPolynomialOrbitGenerators

/-! Two invariant binary coordinates and two twisted scalar coordinates
embed simultaneously into two regular C3 modules. The actual joint map,
not separate dimension maxima, gives uniform generator bound two. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CubicBinaryCoordinateUniform

abbrev Points := Fin 2 × CyclicThree

instance pointAction : MulAction CyclicThree Points where
  smul c x := (x.1,c*x.2)
  one_smul x := by
    change (x.1,1*x.2) = x
    exact Prod.ext rfl (one_mul x.2)
  mul_smul c d x := by
    change (x.1,(c*d)*x.2) = (x.1,c*(d*x.2))
    exact Prod.ext rfl (mul_assoc c d x.2)

abbrev regular := permutationFunctionRepresentation (ZMod 2) CyclicThree Points

def bitCode (u : ZMod 2) (z : ZMod 2 × ZMod 2) (c : CyclicThree) : ZMod 2 :=
  u + (scalarFourTwistAdd (-Multiplicative.toAdd c) z).1

private theorem bitCode_injective : Function.Injective
    (fun p : ZMod 2 × (ZMod 2 × ZMod 2) => bitCode p.1 p.2) := by
  decide +kernel

private theorem bitCode_twisted (u : ZMod 2) (z : ZMod 2 × ZMod 2)
    (g c : CyclicThree) :
    bitCode u (scalarFourTwistAdd (Multiplicative.toAdd g) z) c =
      bitCode u z (g⁻¹*c) := by
  revert u z g c
  decide +kernel

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  {rho : Representation (ZMod 2) CyclicThree V}
  (D : CubicBinaryCoordinates rho)

def embedding : rho.IntertwiningMap regular where
  toLinearMap := {
    toFun := fun v x => bitCode (D.invariant x.1 v) (D.scalar x.1 v) x.2
    map_add' := by
      intro v w
      funext x
      change bitCode (D.invariant x.1 (v+w)) (D.scalar x.1 (v+w)) x.2 =
        bitCode (D.invariant x.1 v) (D.scalar x.1 v) x.2 +
          bitCode (D.invariant x.1 w) (D.scalar x.1 w) x.2
      simp only [bitCode,map_add]
      change D.invariant x.1 v + D.invariant x.1 w +
          ((scalarFourTwistAdd (-Multiplicative.toAdd x.2) (D.scalar x.1 v)).1 +
            (scalarFourTwistAdd (-Multiplicative.toAdd x.2) (D.scalar x.1 w)).1) = _
      abel
    map_smul' := by
      intro a v
      funext x
      fin_cases a <;> simp [bitCode] }
  isIntertwining' g := by
    ext v x
    change bitCode (D.invariant x.1 (rho g v)) (D.scalar x.1 (rho g v)) x.2 =
      bitCode (D.invariant x.1 v) (D.scalar x.1 v) (g⁻¹*x.2)
    rw [D.invariant_fixed,D.scalar_twisted]
    exact bitCode_twisted _ _ _ _

theorem embedding_injective : Function.Injective (embedding D) := by
  intro v w h
  have hslot (j : Fin 2) :
      (D.invariant j v,D.scalar j v) = (D.invariant j w,D.scalar j w) := by
    apply bitCode_injective
    funext c
    exact congrFun h (j,c)
  apply D.joint
  have hi (j : Fin 2) : D.invariant j v = D.invariant j w :=
    congrArg (fun z : ZMod 2 × (ZMod 2 × ZMod 2) => z.1) (hslot j)
  have hs (j : Fin 2) : D.scalar j v = D.scalar j w :=
    congrArg (fun z : ZMod 2 × (ZMod 2 × ZMod 2) => z.2) (hslot j)
  exact Prod.ext (Prod.ext (hi 0) (hi 1)) (Prod.ext (hs 0) (hs 1))

theorem regular_uniform : UniformSubrepresentationGeneratorBound regular 2 := by
  apply permutationFunctionRepresentation_uniform_of_polynomial_orbitCover
    (Multiplicative.ofAdd (1 : ZMod 3)) (fun j : Fin 2 => (j,1))
  intro x
  refine ⟨x.1,(Multiplicative.toAdd x.2).val,?_⟩
  change (x.1,(Multiplicative.ofAdd (1 : ZMod 3)) ^
    (Multiplicative.toAdd x.2).val * 1) = x
  rcases x with ⟨j,c⟩
  congr 1
  revert j c
  decide +kernel

theorem uniform (D : CubicBinaryCoordinates rho) : UniformSubrepresentationGeneratorBound rho 2 :=
  regular_uniform.of_injective (embedding D) (embedding_injective D)

end SymmetricSubgroupAsymptotics.CubicBinaryCoordinateUniform
end
