import SymmetricSubgroupAsymptotics.InducedOrbitStabilizer
import Mathlib.LinearAlgebra.Pi

/-! Mackey decomposition for the actual original finite induced module.
The component at HxP is induced from P∩x⁻¹Hx with the original fibre
acted on by l↦ρ(x l x⁻¹). This module constructs the decomposition and
proves original P-equivariance; neither is a hypothesis. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
variable {k G V : Type} [Field k] [Group G] [Finite G] [AddCommGroup V] [Module k V]
variable (H P : Subgroup G) (ρ : Representation k H V)
variable [Fintype (DoubleCoset.Quotient (H:Set G) (P:Set G))]

abbrev inducedMackeyComponent (q : DoubleCoset.Quotient (H:Set G) (P:Set G)) :=
  Representation.IndV (inducedOrbitStabilizer H P q.out).subtype
    (inducedOrbitFibre H P ρ q.out)

abbrev inducedMackeyComponentAddCommGroup (q : DoubleCoset.Quotient (H:Set G) (P:Set G)) :
    AddCommGroup (inducedMackeyComponent H P ρ q) := by
  dsimp [inducedMackeyComponent,Representation.IndV]
  infer_instance

attribute [local instance] inducedMackeyComponentAddCommGroup

abbrev inducedMackeyComponentModule (q : DoubleCoset.Quotient (H:Set G) (P:Set G)) :
    Module k (inducedMackeyComponent H P ρ q) := by
  dsimp [inducedMackeyComponent,Representation.IndV]
  infer_instance

attribute [local instance] inducedMackeyComponentModule

def inducedMackeyPieceEquiv (q : DoubleCoset.Quotient (H:Set G) (P:Set G)) :
    (coinducedOrbitPiece H P ρ q).toRepresentation.Equiv
      (Representation.ind (inducedOrbitStabilizer H P q.out).subtype
        (inducedOrbitFibre H P ρ q.out)) := by
  have e := inducedOrbitPieceInductionEquiv H P ρ q.out
  have hq := DoubleCoset.out_eq' H P q
  rw [hq] at e
  exact e

def inducedMackeyDecomposition :
    Representation.IndV H.subtype ρ ≃ₗ[k]
      (∀q:DoubleCoset.Quotient (H:Set G) (P:Set G),inducedMackeyComponent H P ρ q) :=
  (inducedOrbitDecomposition H P ρ).trans
    (LinearEquiv.piCongrRight fun q => (inducedMackeyPieceEquiv H P ρ q).toLinearEquiv)

theorem inducedMackeyDecomposition_equivariant (p : P)
    (v : Representation.IndV H.subtype ρ)
    (q : DoubleCoset.Quotient (H:Set G) (P:Set G)) :
    inducedMackeyDecomposition H P ρ ((Representation.ind H.subtype ρ) (p:G) v) q=
      Representation.ind (inducedOrbitStabilizer H P q.out).subtype
        (inducedOrbitFibre H P ρ q.out) p (inducedMackeyDecomposition H P ρ v q) := by
  change inducedMackeyPieceEquiv H P ρ q
      (inducedOrbitDecomposition H P ρ ((Representation.ind H.subtype ρ) (p:G) v) q)=_
  rw [inducedOrbitDecomposition_equivariant]
  exact Representation.IntertwiningMap.isIntertwining _ _
    (inducedMackeyPieceEquiv H P ρ q).toIntertwiningMap p _

end SymmetricSubgroupAsymptotics
