import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction025Generators
import SymmetricSubgroupAsymptotics.CubicRegularSubgroupKernelCoordinates

/-! Five literal point bindings place original action25 in its ACTUAL
regular-two-binary C3 affine subgroup. No48row certificate is imported. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoSixPairAction025RegularPilot
open BinaryThreeQuartetCubicImageSocles
open LinearSemidirectCoprimeSocleBounds LinearSemidirectSubgroupKernelChart
abbrev generators := PrimitiveAffineDegreeTwoSixPairAction025Generators.generators
abbrev Original := Subgroup.closure (Set.range generators)

def pointChart : Plane × CyclicThree ≃ Fin 12 where
  toFun p := (![0, 1, 6, 7, 4, 5, 10, 11, 2, 3, 8, 9] : Fin 12 → Fin 12)
    ⟨4 * (Multiplicative.toAdd p.2).val + (p.1 0).val + 2 * (p.1 1).val, by
      have h0 := ZMod.val_lt (p.1 0)
      have h1 := ZMod.val_lt (p.1 1)
      have hc := ZMod.val_lt (Multiplicative.toAdd p.2)
      omega⟩
  invFun x := ((fun i : Fin 2 =>
    if i=0 then (![0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] : Fin 12 → ZMod 2) x
    else (![0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1] : Fin 12 → ZMod 2) x),
    Multiplicative.ofAdd ((![0, 0, 2, 2, 1, 1, 0, 0, 2, 2, 1, 1] : Fin 12 → ZMod 3) x))
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def offset (j : Fin 5) (x : Bits) : ZMod 2 :=
  if x.1=0 then
    (![![1, 1, 0], ![1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0]] : Fin 5 → Fin 3 → ZMod 2) j ⟨(Multiplicative.toAdd x.2).val,ZMod.val_lt _⟩
  else
    (![![0, 0, 0], ![0, 0, 0], ![1, 1, 0], ![0, 1, 1], ![1, 1, 0]] : Fin 5 → Fin 3 → ZMod 2) j ⟨(Multiplicative.toAdd x.2).val,ZMod.val_lt _⟩

def lifted (j : Fin 5) : Model :=
  ⟨Multiplicative.ofAdd (offset j),Multiplicative.ofAdd (if j=2 then 1 else 0)⟩

theorem binding : ∀ j, literalAction pointChart (lifted j) = generators j := by
  intro j
  apply Equiv.ext
  intro x
  revert j x
  decide +kernel

abbrev K : Subgroup Model := Subgroup.closure (Set.range lifted)

theorem projection_surjective : Function.Surjective (projection linear K) := by
  intro c
  have hp : ∃ m : Fin 3, (Multiplicative.ofAdd (1 : ZMod 3))^m.val = c := by
    revert c
    decide +kernel
  obtain ⟨m,hm⟩ := hp
  refine ⟨closureGenerators lifted 2 ^ m.val,?_⟩
  rw [map_pow]
  change (lifted 2).right ^ m.val = c
  exact hm

theorem scalar_nonzero : ∃ j : Fin 2, ∃ p : (projection linear K).ker,
    CubicElementaryKernelCoordinates.scalar (projection linear K)
      (CubicRegularSubgroupKernelCoordinates.moduleRep K projection_surjective).ρ
      (CubicRegularSubgroupKernelCoordinates.originalKernelChart K projection_surjective).equiv.symm
      (CubicRegularSubgroupKernelCoordinates.coordinates K projection_surjective) j p ≠ 1 := by
  refine ⟨0,⟨closureGenerators lifted 0,by rfl⟩,?_⟩
  change Multiplicative.ofAdd
    (CubicRegularBinaryCoordinates.scalar 0 ((lifted 0).left.toAdd)) ≠ 1
  decide +kernel

end PrimitiveAffineDegreeTwoSixPairAction025RegularPilot
end SymmetricSubgroupAsymptotics
end
