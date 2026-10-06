import SymmetricSubgroupAsymptotics.InducedOrbitDecomposition
import SymmetricSubgroupAsymptotics.PermutationalWreathLinearRepresentation

/-!
# A full wreath frame as a coinduced module

Evaluation at one top point identifies the full function representation of
a transitive permutational wreath subgroup with its local coinduced model.
For the finite-frame importer only the injective direction is needed.  This
construction removes all row-specific representation theory from the
actual-to-emitted frame comparison: the emitted coset table only has to
identify the resulting coinduced model with its checked matrix row.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PermutationalWreathProduct
namespace FunctionCoinduced

variable {k A D Q I V : Type}
  [Field k] [Group A] [Group D] [Group Q]
  [MulAction Q I]
  [AddCommGroup V] [Module k V]
  (rho : A →* PermutationalWreathProduct D Q I)
  (sigma : Representation k D V)
  (i₀ : I)

/-- The preimage in the acting group of the chosen top-point stabilizer. -/
def stabilizer : Subgroup A :=
  (MulAction.stabilizer Q i₀).comap
    ((rightHom (D := D) (Q := Q) (I := I)).comp rho)

/-- The literal base coordinate seen by an element fixing `i₀`. -/
def stabilizerComponent : stabilizer rho i₀ →* D where
  toFun h := (rho h.1).left i₀
  map_one' := by simp
  map_mul' x y := by
    change (rho (x.1 * y.1)).left i₀ =
      (rho x.1).left i₀ * (rho y.1).left i₀
    rw [map_mul, mul_left]
    have hx : (rho x.1).right⁻¹ • i₀ = i₀ := by
      have hx0 : (rho x.1).right • i₀ = i₀ := x.2
      calc
        (rho x.1).right⁻¹ • i₀ =
            (rho x.1).right⁻¹ • ((rho x.1).right • i₀) :=
          congrArg ((rho x.1).right⁻¹ • ·) hx0.symm
        _ = i₀ := inv_smul_smul _ _
    simp only [Pi.mul_apply, hx]

/-- The local linear action attached to the chosen top point. -/
def localRepresentation : Representation k (stabilizer rho i₀) V :=
  sigma.comp (stabilizerComponent rho i₀)

/-- The full function representation restricted to the subgroup `A`. -/
def fullRepresentation : Representation k A (I → V) :=
  (functionRepresentation (Q := Q) (I := I) sigma).comp rho

/-- Evaluate every translated frame at `i₀`.  The covariance condition is
exactly the defining condition for the coinduced representation. -/
def toCoinducedLinear :
    (I → V) →ₗ[k]
      Representation.coindV (stabilizer rho i₀).subtype
        (localRepresentation rho sigma i₀) where
  toFun f := ⟨fun a => fullRepresentation rho sigma a f i₀, by
    intro h a
    have hh : (rho h.1).right • i₀ = i₀ := h.2
    have hhInv : (rho h.1).right⁻¹ • i₀ = i₀ := by
      calc
        (rho h.1).right⁻¹ • i₀ =
            (rho h.1).right⁻¹ • ((rho h.1).right • i₀) :=
          congrArg ((rho h.1).right⁻¹ • ·) hh.symm
        _ = i₀ := inv_smul_smul _ _
    change functionRepresentation (Q := Q) (I := I) sigma
        (rho (h.1 * a)) f i₀ =
      sigma ((rho h.1).left i₀)
        (functionRepresentation (Q := Q) (I := I) sigma (rho a) f i₀)
    rw [map_mul]
    simp only [functionRepresentation_apply, hhInv, map_mul,
      Module.End.mul_apply]
  ⟩
  map_add' f g := by
    apply Subtype.ext
    funext a
    change fullRepresentation rho sigma a (f + g) i₀ =
      fullRepresentation rho sigma a f i₀ +
        fullRepresentation rho sigma a g i₀
    exact congrFun ((fullRepresentation rho sigma a).map_add f g) i₀
  map_smul' c f := by
    apply Subtype.ext
    funext a
    change fullRepresentation rho sigma a (c • f) i₀ =
      c • fullRepresentation rho sigma a f i₀
    exact congrFun ((fullRepresentation rho sigma a).map_smul c f) i₀

/-- Evaluation is equivariant for the ambient `A`-action. -/
theorem toCoinducedLinear_equivariant (a : A) (f : I → V) :
    toCoinducedLinear rho sigma i₀ (fullRepresentation rho sigma a f) =
      Representation.coind (stabilizer rho i₀).subtype
        (localRepresentation rho sigma i₀) a
        (toCoinducedLinear rho sigma i₀ f) := by
  apply Subtype.ext
  funext g
  change fullRepresentation rho sigma g
      (fullRepresentation rho sigma a f) i₀ =
    fullRepresentation rho sigma (g * a) f i₀
  rw [map_mul, Module.End.mul_apply]

/-- The full-frame evaluation, packaged as an intertwiner. -/
def toCoinduced :
    (fullRepresentation rho sigma).IntertwiningMap
      (Representation.coind (stabilizer rho i₀).subtype
        (localRepresentation rho sigma i₀)) where
  toLinearMap := toCoinducedLinear rho sigma i₀
  isIntertwining' a := by
    apply LinearMap.ext
    exact toCoinducedLinear_equivariant rho sigma i₀ a

/-- Surjectivity onto a transitive top makes evaluation at one point detect
every full-frame coordinate. -/
theorem toCoinduced_injective
    [MulAction.IsPretransitive Q I]
    (htop : Function.Surjective
      ((rightHom (D := D) (Q := Q) (I := I)).comp rho)) :
    Function.Injective (toCoinduced rho sigma i₀) := by
  intro f g hfg
  funext j
  obtain ⟨q, hq⟩ := MulAction.exists_smul_eq Q j i₀
  obtain ⟨a, ha⟩ := htop q
  change (rho a).right = q at ha
  have hpoint : (rho a).right⁻¹ • i₀ = j := by
    rw [ha]
    calc
      q⁻¹ • i₀ = q⁻¹ • (q • j) := congrArg (q⁻¹ • ·) hq.symm
      _ = j := inv_smul_smul _ _
  have he := congrArg
    (fun u : Representation.coindV (stabilizer rho i₀).subtype
      (localRepresentation rho sigma i₀) => u.1 a) hfg
  change sigma ((rho a).left i₀)
      (f ((rho a).right⁻¹ • i₀)) =
    sigma ((rho a).left i₀)
      (g ((rho a).right⁻¹ • i₀)) at he
  exact (sigma.apply_bijective ((rho a).left i₀)).injective
    (by simpa only [hpoint] using he)

section FiniteIndex

variable [(stabilizer rho i₀).FiniteIndex]

/-- The same literal map in Mathlib's induced-function model.  Generated
frame rows use right-coset representatives, so this is the convenient
boundary for checking their matrices. -/
def toInduced :
    (fullRepresentation rho sigma).IntertwiningMap
      (Representation.ind (stabilizer rho i₀).subtype
        (localRepresentation rho sigma i₀)) :=
  (inducedToCoinducedEquiv (stabilizer rho i₀)
      (localRepresentation rho sigma i₀)).symm.toIntertwiningMap.comp
    (toCoinduced rho sigma i₀)

/-- The induced form retains injectivity. -/
theorem toInduced_injective
    [MulAction.IsPretransitive Q I]
    (htop : Function.Surjective
      ((rightHom (D := D) (Q := Q) (I := I)).comp rho)) :
    Function.Injective (toInduced rho sigma i₀) :=
  (inducedToCoinducedEquiv (stabilizer rho i₀)
      (localRepresentation rho sigma i₀)).symm.injective.comp
    (toCoinduced_injective rho sigma i₀ htop)

end FiniteIndex

end FunctionCoinduced
end PermutationalWreathProduct
end SymmetricSubgroupAsymptotics

end
