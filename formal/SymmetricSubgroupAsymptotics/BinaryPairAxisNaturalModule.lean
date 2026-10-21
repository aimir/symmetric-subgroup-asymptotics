import SymmetricSubgroupAsymptotics.BinaryPairAxisRadicalSpace
import SymmetricSubgroupAsymptotics.PermutationSubrepresentationHead

/-! The same original axis, regarded directly as a subrepresentation of
the natural function module on the actual top's original point set. Both
the original normal generator rank and its whole-ambient radical persist. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} {w : ℕ} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U (Fin w)) (B : Subgroup U) [B.Normal]

/-- No new module state is selected: its vectors are the literal bits of
this original B inside the same original pair kernel. -/
def axisNaturalSubrepresentation :
    Subrepresentation (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin w)) where
  toSubmodule := F.ambientAxis B
  apply_mem_toSubmodule t v hv := by
    change F.coordinateTopAction t v ∈ F.ambientAxis B
    exact (F.axisSubrepresentation B).apply_mem_toSubmodule t hv

theorem axisNatural_representation :
    (F.axisNaturalSubrepresentation B).toRepresentation =
      (F.axisSubrepresentation B).toRepresentation := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  rfl

/-- Literal normal rank equals the head of the natural-module axis. -/
theorem axisNatural_normalGen [Finite X] (hB : B ≤ F.top.ker) (hU : IsPGroup 2 U) :
    MarkedC4.normalGen B =
      Module.finrank (ZMod 2) (F.axisNaturalSubrepresentation B).toRepresentation.Coinvariants := by
  rw [F.axisNatural_representation]
  exact F.axis_normalGen_eq_coinvariants B hB hU

/-- The original relative radical is exactly the intrinsic natural-module
radical in the same original point coordinates. -/
theorem axisNatural_radical (hB : B ≤ F.top.ker) :
    F.ambientAxis (primeRelativeRadical 2 B) =
      (Representation.Coinvariants.ker (F.axisNaturalSubrepresentation B).toRepresentation).map
        (F.axisNaturalSubrepresentation B).toSubmodule.subtype := by
  rw [F.axisNatural_representation]
  exact F.ambientAxis_radical_eq_coinvariants_radical B hB

end SymmetricSubgroupAsymptotics.BinaryPairFrame
