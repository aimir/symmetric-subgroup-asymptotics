import SymmetricSubgroupAsymptotics.CoinducedLeadingCoordinates
import SymmetricSubgroupAsymptotics.InducedOrbitDecomposition

/-!
# Finite right-coset coordinates for an induced frame

The eight-frame finite certificates store a right transversal and the
corresponding Schreier twists.  This file removes the generic linear-algebra
part of their importer.  Mathlib's induction--coinduction equivalence first
places the induced module in the function model; evaluation on the retained
right transversal then gives the literal coset-major coordinate map.

Only exact right-coset factorization is needed for injectivity.  The
row-specific generator equations remain finite certificate obligations.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace EightFrameInducedCoordinates

variable {k G V : Type} [Field k] [Group G]
  [AddCommGroup V] [Module k V]
  {N d : ℕ}

set_option maxHeartbeats 800000 in
/-- An equivalence of local representations induces an equivalence of the
two corresponding ambient induced representations. -/
noncomputable def inducedEquivOfLocalEquiv
    {W : Type} [AddCommGroup W] [Module k W]
    (H : Subgroup G)
    (rho : Representation k H V) (sigma : Representation k H W)
    (e : rho.Equiv sigma) :
    (Representation.ind H.subtype rho).Equiv
      (Representation.ind H.subtype sigma) :=
  Representation.equivOfIso
    ((Rep.indFunctor k H.subtype).mapIso (Rep.mkIso e))

/-- Coset-major coordinates on an induced module, obtained through the
canonical finite-index induction--coinduction equivalence. -/
def coordinates
    (H : Subgroup G) [H.FiniteIndex]
    (rho : Representation k H V)
    (T : Fin N → G) (basis : Module.Basis (Fin d) k V) :
    Representation.IndV H.subtype rho →ₗ[k] (Fin (N * d) → k) :=
  (CoinducedLeadingCoordinates.coordinates H rho T basis).comp
    (inducedToCoinducedEquiv (k := k) (G := G) H rho).toLinearEquiv.toLinearMap

@[simp] theorem coordinates_label
    (H : Subgroup G) [H.FiniteIndex]
    (rho : Representation k H V)
    (T : Fin N → G) (basis : Module.Basis (Fin d) k V)
    (v : Representation.IndV H.subtype rho)
    (a : Fin N) (i : Fin d) :
    coordinates H rho T basis v
        (CoinducedLeadingCoordinates.label a i) =
      basis.equivFun
        (((inducedToCoinducedEquiv (k := k) (G := G) H rho) v).1 (T a)) i := by
  exact CoinducedLeadingCoordinates.coordinates_label H rho T basis
    ((inducedToCoinducedEquiv (k := k) (G := G) H rho) v) a i

/-- A complete literal right transversal makes the coordinate map
injective.  No group-order or representation-classification input enters
this step. -/
theorem coordinates_injective
    (H : Subgroup G) [H.FiniteIndex]
    (rho : Representation k H V)
    (T : Fin N → G) (basis : Module.Basis (Fin d) k V)
    (hfactor : ∀ x : G, ∃ h : G, h ∈ H ∧ ∃ a : Fin N, x = h * T a) :
    Function.Injective (coordinates H rho T basis) :=
  (CoinducedLeadingCoordinates.coordinates_injective
      H rho T basis hfactor).comp
    (inducedToCoinducedEquiv (k := k) (G := G) H rho).injective

/-- First change the local fibre through an explicit representation
equivalence, then take the retained right-coset coordinates.  This is the
form used by the order-three binary-plane comparison. -/
def coordinatesOfLocalEquiv
    {W : Type} [AddCommGroup W] [Module k W]
    (H : Subgroup G) [H.FiniteIndex]
    (rho : Representation k H V) (sigma : Representation k H W)
    (e : rho.Equiv sigma)
    (T : Fin N → G) (basis : Module.Basis (Fin d) k W) :
    Representation.IndV H.subtype rho →ₗ[k] (Fin (N * d) → k) :=
  (coordinates H sigma T basis).comp
    (inducedEquivOfLocalEquiv (k := k) (G := G) (V := V)
      H rho sigma e).toLinearEquiv.toLinearMap

/-- Exact coset factorization and the local representation equivalence make
the transported coordinate map injective. -/
theorem coordinatesOfLocalEquiv_injective
    {W : Type} [AddCommGroup W] [Module k W]
    (H : Subgroup G) [H.FiniteIndex]
    (rho : Representation k H V) (sigma : Representation k H W)
    (e : rho.Equiv sigma)
    (T : Fin N → G) (basis : Module.Basis (Fin d) k W)
    (hfactor : ∀ x : G, ∃ h : G, h ∈ H ∧ ∃ a : Fin N, x = h * T a) :
    Function.Injective
      (coordinatesOfLocalEquiv H rho sigma e T basis) :=
  (coordinates_injective H sigma T basis hfactor).comp
    (inducedEquivOfLocalEquiv (k := k) (G := G) (V := V)
      H rho sigma e).injective

end EightFrameInducedCoordinates
end SymmetricSubgroupAsymptotics

end
