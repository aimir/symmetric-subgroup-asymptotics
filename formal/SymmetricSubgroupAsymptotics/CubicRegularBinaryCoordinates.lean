import SymmetricSubgroupAsymptotics.CubicBinaryCoordinateUniform

/-! Canonical trace/twisted decomposition of two regular F2[C3] modules.
The three bits (a,b,c) become (a+b+c,(b+c,a+b)). -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CubicRegularBinaryCoordinates
open CubicBinaryCoordinateUniform

abbrev Vector := Points → ZMod 2
private abbrev c0 : CyclicThree := Multiplicative.ofAdd 0
private abbrev c1 : CyclicThree := Multiplicative.ofAdd 1
private abbrev c2 : CyclicThree := Multiplicative.ofAdd 2

private def evaluation (j : Fin 2) (c : CyclicThree) : Vector →ₗ[ZMod 2] ZMod 2 :=
  LinearMap.proj (j,c)

def invariant (j : Fin 2) : Vector →ₗ[ZMod 2] ZMod 2 :=
  evaluation j c0 + evaluation j c1 + evaluation j c2

def scalar (j : Fin 2) : Vector →ₗ[ZMod 2] (ZMod 2 × ZMod 2) :=
  (evaluation j c1 + evaluation j c2).prod
    (evaluation j c0 + evaluation j c1)

private theorem decode : ∀ (v : Vector) (j : Fin 2) (c : CyclicThree),
    bitCode (invariant j v) (scalar j v) c = v (j,c) := by
  decide +kernel

def coordinates : CubicBinaryCoordinates regular where
  invariant := invariant
  scalar := scalar
  invariant_fixed := by
    intro c v j
    revert c v j
    decide +kernel
  scalar_twisted := by
    intro c v j
    revert c v j
    decide +kernel
  joint := by
    intro v w he
    have hi : ∀ j : Fin 2, invariant j v = invariant j w := by
      intro j
      fin_cases j
      · exact congrArg (fun z : (ZMod 2 × ZMod 2) ×
          ((ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2)) => z.1.1) he
      · exact congrArg (fun z : (ZMod 2 × ZMod 2) ×
          ((ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2)) => z.1.2) he
    have hs : ∀ j : Fin 2, scalar j v = scalar j w := by
      intro j
      fin_cases j
      · exact congrArg (fun z : (ZMod 2 × ZMod 2) ×
          ((ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2)) => z.2.1) he
      · exact congrArg (fun z : (ZMod 2 × ZMod 2) ×
          ((ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2)) => z.2.2) he
    funext x
    rw [← decode v x.1 x.2,← decode w x.1 x.2,hi,hs]

end SymmetricSubgroupAsymptotics.CubicRegularBinaryCoordinates
end
