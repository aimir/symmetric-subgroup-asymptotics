import SymmetricSubgroupAsymptotics.PGroupInducedMiddleHead
import SymmetricSubgroupAsymptotics.InducedTernaryHead
import SymmetricSubgroupAsymptotics.PGroupCoinvariantGenerators
import SymmetricSubgroupAsymptotics.RepresentationGeneratorRestrictionMaschke

/-! Actual uniform generators from the full Sylow/Mackey middle-width
sum.  The original module is restricted, not replaced by its ambient head. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics
attribute [local instance] inducedMackeyComponentAddCommGroup inducedMackeyComponentModule

variable {p : ℕ} [Fact p.Prime] {G V : Type} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]

/-- The local index equalities are the literal actual Sylow-stabilizer
indices supplied by inducedMackeySylow_indices. -/
theorem induced_sylow_middle_uniform
    (H : Subgroup G) (P : Sylow p G) (rho : Representation (ZMod p) H V)
    [Fintype (DoubleCoset.Quotient (H : Set G) ((P : Subgroup G) : Set G))]
    (j : DoubleCoset.Quotient (H : Set G) ((P : Subgroup G) : Set G) → ℕ)
    (hindex : ∀ q,(inducedOrbitStabilizer H (P : Subgroup G) q.out).index=p^j q) :
    UniformSubrepresentationGeneratorBound (Representation.ind H.subtype rho)
      (∑ q,Module.finrank (ZMod p) V*primeGridMiddleWidth p (j q)) := by
  letI : Finite V := Module.finite_of_finite (ZMod p)
  letI := induced_finiteDimensional H rho
  letI : Finite (Representation.IndV H.subtype rho) := Module.finite_of_finite (ZMod p)
  intro M
  letI : Finite M.toSubmodule := Finite.of_injective
    M.toSubmodule.subtype M.toSubmodule.injective_subtype
  have hhead : Module.finrank (ZMod p)
      (Representation.IntertwiningMap
        (M.toRepresentation.comp (P : Subgroup G).subtype : Representation (ZMod p) P M.toSubmodule)
        (Representation.trivial (ZMod p) P (ZMod p)))≤
        ∑ q,Module.finrank (ZMod p) V*primeGridMiddleWidth p (j q) := by
    apply representationHom_finrank_le_coordinates
      (fun q => inducedMackeyComponent H (P : Subgroup G) rho q)
      (M.toRepresentation.comp (P : Subgroup G).subtype)
      (fun q => Representation.ind
        (inducedOrbitStabilizer H (P : Subgroup G) q.out).subtype
        (inducedOrbitFibre H (P : Subgroup G) rho q.out))
      (Representation.trivial (ZMod p) P (ZMod p))
      (fun q => Module.finrank (ZMod p) V*primeGridMiddleWidth p (j q))
      (fun q S => pGroup_induced_subrepresentationHead_le_middle p P.isPGroup'
        (inducedOrbitStabilizer H (P : Subgroup G) q.out)
        (inducedOrbitFibre H (P : Subgroup G) rho q.out) (j q) (hindex q) S)
      (inducedMackeySubmoduleCoordinate H (P : Subgroup G) rho M)
      (inducedMackeySubmoduleCoordinate_injective H (P : Subgroup G) rho M)
  have hgen := pGroup_representationGeneratedBy_coinvariants P.isPGroup'
    (M.toRepresentation.comp (P : Subgroup G).subtype)
  rw [←representationHead_finrank_eq_coinvariants] at hgen
  exact RepresentationGeneratedBy.of_comp M.toRepresentation (P : Subgroup G).subtype
    (representationGeneratedBy_mono _ hhead hgen)

end SymmetricSubgroupAsymptotics
