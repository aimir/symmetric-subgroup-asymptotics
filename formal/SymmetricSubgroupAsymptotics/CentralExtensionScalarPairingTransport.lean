import SymmetricSubgroupAsymptotics.CentralExtensionScalarPairingIndex

/-! Transport an already proved actual central-extension datum through
an explicit group equivalence. No new pairing or group recognition is
postulated. This is useful for a subgroupOf copy of a normal radical. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CentralExtensionScalarPairingTransport
open CentralExtensionScalarPairingIndex
variable {F V N R : Type*} [Field F] [AddCommGroup V] [Module F V] [Group N] [Group R]

def transport (D : Data (F := F) (V := V) (N := N)) (e : R ≃* N) :
    Data (F := F) (V := V) (N := R) where
  projection := D.projection.comp e.toMonoidHom
  central := e.symm.toMonoidHom.comp D.central
  central_injective := e.symm.injective.comp D.central_injective
  central_range := by
    ext u
    constructor
    · rintro ⟨a,rfl⟩
      change D.projection (e (e.symm (D.central a))) = 1
      rw [e.apply_symm_apply]
      exact D.central_range.le ⟨a,rfl⟩
    · intro hu
      have hu' : e u ∈ D.projection.ker := hu
      obtain ⟨a,ha⟩ := D.central_range.symm.le hu'
      refine ⟨a,?_⟩
      apply e.injective
      exact (e.apply_symm_apply _).trans ha
  projection_surjective := D.projection_surjective.comp e.surjective
  pairing := D.pairing
  alternating := D.alternating
  full := D.full
  commutator := by
    intro x y
    apply e.injective
    change e (x*y*x⁻¹*y⁻¹) = e (e.symm (D.central (Multiplicative.ofAdd
      (D.pairing (D.projection (e x)).toAdd (D.projection (e y)).toAdd))))
    rw [e.apply_symm_apply]
    simpa only [map_mul,map_inv] using D.commutator (e x) (e y)

theorem projection_apply (D : Data (F := F) (V := V) (N := N)) (e : R ≃* N) (u : R) :
    (transport D e).projection u = D.projection (e u) := rfl

theorem central_apply (D : Data (F := F) (V := V) (N := N)) (e : R ≃* N)
    (a : Multiplicative F) : (transport D e).central a = e.symm (D.central a) := rfl

end SymmetricSubgroupAsymptotics.CentralExtensionScalarPairingTransport
