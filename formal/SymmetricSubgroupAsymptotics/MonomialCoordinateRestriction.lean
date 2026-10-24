import SymmetricSubgroupAsymptotics.MonomialActualCoefficients

/-! Equivariant coordinate maps restrict the same actual monomial
representation. The restricted coefficients satisfy the representation
laws because they were extracted from the original operators. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MonomialCoordinateRestriction
open MonomialActualCoefficients

variable {k G I Y : Type} [Field k] [Group G]
    [Fintype I] [DecidableEq I] [MulAction G I] [MulAction G Y]
    (rho : Representation k G (I → k))
    (hdelta : ∀ g : G, ∀ i : I, ∃ u : kˣ,
      rho g (Pi.single i 1) = (u : k) • (Pi.single (g • i) 1 : I → k))
    (j : Y → I) (hj : ∀ g : G, ∀ y : Y, j (g • y) = g • j y)

def operator (g : G) : Module.End k (Y → k) where
  toFun v y := coefficient rho g (j y) * v (g⁻¹ • y)
  map_add' v w := by
    funext y
    exact mul_add _ _ _
  map_smul' a v := by
    funext y
    exact mul_left_comm _ _ _

/-- This is an actual representation, not a supplied coordinate action. -/
def representation : Representation k G (Y → k) where
  toFun := operator rho j
  map_one' := by
    apply LinearMap.ext
    intro v
    funext y
    change coefficient rho 1 (j y) * v ((1 : G)⁻¹ • y) = v y
    rw [coefficient_one,inv_one,one_smul,one_mul]
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    funext y
    change coefficient rho (g*h) (j y) * v ((g*h)⁻¹ • y) =
      coefficient rho g (j y) *
        (coefficient rho h (j (g⁻¹ • y)) * v (h⁻¹ • (g⁻¹ • y)))
    rw [coefficient_mul rho hdelta,hj,mul_inv_rev,mul_smul,mul_assoc]

theorem representation_apply (g : G) (v : Y → k) (y : Y) :
    representation rho hdelta j hj g v y =
      coefficient rho g (j y) * v (g⁻¹ • y) := rfl

/-- Literal coordinate restriction intertwines the two actual actions. -/
def restriction : rho.IntertwiningMap (representation rho hdelta j hj) where
  toLinearMap := {
    toFun v y := v (j y)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    funext y
    change rho g v (j y) = coefficient rho g (j y) * v (j (g⁻¹ • y))
    rw [action_apply rho hdelta,hj]

theorem restriction_apply (v : I → k) (y : Y) :
    restriction rho hdelta j hj v y = v (j y) := rfl

theorem monomial (g : G) (y : Y) : ∃ u : kˣ,
    representation rho hdelta j hj g (Pi.single y 1) =
      (u : k) • (Pi.single (g • y) 1 : Y → k) := by
  let c := coefficient rho g (j (g • y))
  have hc : c ≠ 0 := coefficient_ne_zero rho hdelta g (j (g • y))
  refine ⟨Units.mk0 c hc,?_⟩
  funext z
  change coefficient rho g (j z) * (Pi.single y 1 : Y → k) (g⁻¹ • z) =
    (↑(Units.mk0 c hc) : k) * (Pi.single (g • y) 1 : Y → k) z
  by_cases hz : z = g • y
  · subst z
    rw [inv_smul_smul,Pi.single_eq_same,Pi.single_eq_same,mul_one,mul_one]
    rfl
  · have hn : g⁻¹ • z ≠ y := by
      intro h
      apply hz
      calc
        z = g • (g⁻¹ • z) := (smul_inv_smul _ _).symm
        _ = g • y := congrArg (fun a => g • a) h
    rw [Pi.single_eq_of_ne hn,Pi.single_eq_of_ne hz,mul_zero,mul_zero]

/-- Transitivity is required only on the displayed actual coordinate orbit. -/
theorem uniform [Finite G] [Fintype Y] [Nontrivial Y]
    [MulAction.IsPretransitive G Y] :
    UniformSubrepresentationGeneratorBound (representation rho hdelta j hj)
      (Nat.card Y / 2) :=
  MonomialPolynomialOrbitGenerators.uniform_of_transitive
    (representation rho hdelta j hj) (monomial rho hdelta j hj)

end SymmetricSubgroupAsymptotics.MonomialCoordinateRestriction
