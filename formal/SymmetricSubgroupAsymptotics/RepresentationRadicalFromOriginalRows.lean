import SymmetricSubgroupAsymptotics.RepresentationRadicalFromTrivialQuotientSaturation
import SymmetricSubgroupAsymptotics.BinaryBitmaskCoordinates
import Mathlib.Algebra.Field.ZMod

/-! A checked original affine-row packet identifies the entire original
radical once its intrinsic head cap saturates the displayed dimensions.
The rows cover the original group, and all basis displacement equations
are for the same original representation. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem representation_radical_eq_of_original_rows_basis
    {G : Type} [Group G] {n d e r c : ℕ}
    (rho : Representation (ZMod 2) G (Fin n → ZMod 2))
    (W : Subrepresentation rho) (S : BinaryCoordinateSpace n d) (R : BinaryCoordinateSpace n e)
    (row : Fin r → G) (hrow : Function.Surjective row)
    (action : Fin r → (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (hact : ∀ i, rho (row i) = action i)
    (hS : W.toSubmodule = S.space)
    (hkill : ∀ i j, action i (S.inclusion (Pi.single j 1)) -
      S.inclusion (Pi.single j 1) ∈ R.space)
    (hcap : Module.finrank (ZMod 2) W.toRepresentation.Coinvariants ≤ c)
    (hdim : d = e + c) :
    (Representation.Coinvariants.ker W.toRepresentation).map W.toSubmodule.subtype = R.space := by
  refine representation_radical_eq_of_trivial_quotient_head_cap rho W R.space ?_ c hcap ?_
  · intro g v hv
    obtain ⟨i, rfl⟩ := hrow g
    rw [hact]
    rw [hS] at hv
    have hm : v ∈ R.space.comap
        ((action i : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) - LinearMap.id) :=
      (S.le_of_basis_mem _ (fun j => by
        change action i (S.inclusion (Pi.single j 1)) - S.inclusion (Pi.single j 1) ∈ R.space
        exact hkill i j)) hv
    exact hm
  · rw [hS, S.finrank, R.finrank]
    exact hdim

end SymmetricSubgroupAsymptotics
