import SymmetricSubgroupAsymptotics.PermutationalWreathFunctionCoinduced
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The full actual function frame is the whole coinduced frame.
A single transporter for each physical point gives an injection in the
reverse direction; finite-dimensional rank then proves that the original
intertwiner is surjective. No invariant-submodule enumeration is used. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PermutationalWreathProduct.FunctionCoinduced

variable {k A D Q I V : Type}
    [Field k] [Group A] [Group D] [Group Q] [MulAction Q I]
    [AddCommGroup V] [Module k V]
    (rho : A →* PermutationalWreathProduct D Q I)
    (sigma : Representation k D V) (i₀ : I)
    [htrans : MulAction.IsPretransitive Q I]
    (htop : Function.Surjective
      ((rightHom (D := D) (Q := Q) (I := I)).comp rho))

include htop htrans

private theorem transporter_exists (j : I) : ∃ a : A, (rho a).right⁻¹ • i₀ = j := by
  obtain ⟨q, hq⟩ := MulAction.exists_smul_eq Q j i₀
  obtain ⟨a, ha⟩ := htop q
  change (rho a).right = q at ha
  refine ⟨a, ?_⟩
  rw [ha]
  calc
    q⁻¹ • i₀ = q⁻¹ • (q • j) := congrArg (q⁻¹ • ·) hq.symm
    _ = j := inv_smul_smul _ _

private def transporter (j : I) : A :=
  Classical.choose (transporter_exists rho i₀ htop j)

private theorem transporter_spec (j : I) :
    (rho (transporter rho i₀ htop j)).right⁻¹ • i₀ = j :=
  Classical.choose_spec (transporter_exists rho i₀ htop j)

private def transversalEvaluation :
    Representation.coindV (stabilizer rho i₀).subtype
      (localRepresentation rho sigma i₀) →ₗ[k] (I → V) where
  toFun f j := f.1 (transporter rho i₀ htop j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem transversalEvaluation_injective :
    Function.Injective (transversalEvaluation rho sigma i₀ htop) := by
  intro f z hfz
  apply Subtype.ext
  funext a
  let j : I := (rho a).right⁻¹ • i₀
  let c : A := transporter rho i₀ htop j
  have hc : (rho c).right⁻¹ • i₀ = j := transporter_spec rho i₀ htop j
  have hh : a * c⁻¹ ∈ stabilizer rho i₀ := by
    change (rho (a * c⁻¹)).right • i₀ = i₀
    rw [map_mul, map_inv]
    change ((rho a).right * (rho c).right⁻¹) • i₀ = i₀
    rw [mul_smul, hc]
    exact smul_inv_smul (rho a).right i₀
  let h : stabilizer rho i₀ := ⟨a * c⁻¹, hh⟩
  have hprod : (h : A) * c = a := by
    change (a * c⁻¹) * c = a
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  have hf := f.2 h c
  have hz := z.2 h c
  change f.1 ((h : A) * c) = _ at hf
  change z.1 ((h : A) * c) = _ at hz
  rw [hprod] at hf hz
  have he : f.1 c = z.1 c := congrFun hfz j
  exact hf.trans ((congrArg (localRepresentation rho sigma i₀ h) he).trans hz.symm)

/-- The original full-frame map is onto the original coinduced module. -/
theorem toCoinduced_surjective
    [Finite A] [Fintype I] [FiniteDimensional k V] :
    Function.Surjective (toCoinduced rho sigma i₀) := by
  letI : Fintype A := Fintype.ofFinite A
  letI : FiniteDimensional k
      (Representation.coindV (stabilizer rho i₀).subtype
        (localRepresentation rho sigma i₀)) :=
    FiniteDimensional.of_injective
      (Representation.coindV (stabilizer rho i₀).subtype
        (localRepresentation rho sigma i₀)).subtype Subtype.val_injective
  have hi := toCoinduced_injective rho sigma i₀ htop
  have hforward := (toCoinduced rho sigma i₀).toLinearMap.finrank_le_finrank_of_injective hi
  have hreverse := (transversalEvaluation rho sigma i₀ htop).finrank_le_finrank_of_injective
    (transversalEvaluation_injective rho sigma i₀ htop)
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (toCoinduced rho sigma i₀).toLinearMap) (Nat.le_antisymm hforward hreverse)).mp hi

def fullCoinducedEquiv [Finite A] [Fintype I] [FiniteDimensional k V] :
    (fullRepresentation rho sigma).Equiv
      (Representation.coind (stabilizer rho i₀).subtype
        (localRepresentation rho sigma i₀)) :=
  (toCoinduced rho sigma i₀).ofBijective
    ⟨toCoinduced_injective rho sigma i₀ htop, toCoinduced_surjective rho sigma i₀ htop⟩

end SymmetricSubgroupAsymptotics.PermutationalWreathProduct.FunctionCoinduced

end
