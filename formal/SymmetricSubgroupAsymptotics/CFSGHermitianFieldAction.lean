import SymmetricSubgroupAsymptotics.CFSGHermitianSemilinearPiece
import SymmetricSubgroupAsymptotics.CFSGProjectiveFieldAction
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldSemilinearDimension

/-! Coordinate field automorphisms preserving the literal form matrix
and commuting with its involution act on its actual singular lines.
No polar-space extension theorem is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGHermitianFieldAction
open CFSGTwistedAUnitaryParameters CFSGHermitianOrthogonalSpan CFSGProjectiveFieldAction
variable {K I : Type*} [Field K] [Fintype I]
local instance (tau : K ≃+* K) : RingHomSurjective tau.toRingHom := ⟨tau.surjective⟩
local instance (tau : K ≃+* K) : RingHomInvPair tau.toRingHom tau.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv tau
local instance (tau : K ≃+* K) : RingHomInvPair tau.symm.toRingHom tau.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm tau
variable (sigma tau : K ≃+* K) (H : Matrix I I K)
variable (hcomm : Function.Commute sigma tau) (hH : H.map tau = H)
include hcomm hH

theorem pair_map (v w : I → K) :
    hermitianPair sigma H (coordinateEquiv tau v) (coordinateEquiv tau w) =
      tau (hermitianPair sigma H v w) := by
  symm
  change tau.toRingHom (dotProduct (sigma ∘ v) (H *ᵥ w)) = _
  rw [RingHom.map_dotProduct]
  have hv : tau.toRingHom ∘ (sigma ∘ v) = sigma ∘ (tau ∘ v) := by
    funext i
    exact (hcomm (v i)).symm
  have hw : tau.toRingHom ∘ (H *ᵥ w) = H *ᵥ (tau ∘ w) := by
    funext i
    have he := RingHom.map_mulVec tau.toRingHom H w i
    change tau ((H *ᵥ w) i) = (H.map tau *ᵥ (tau ∘ w)) i at he
    rw [hH] at he
    exact he
  rw [hv,hw]
  rfl

theorem singular_map_iff (P : Submodule K (I → K)) :
    (∀ x ∈ P.map (coordinateEquiv tau).toLinearMap, hermitianPair sigma H x x = 0) ↔
      ∀ x ∈ P, hermitianPair sigma H x x = 0 := by
  constructor
  · intro h x hx
    apply tau.injective
    rw [map_zero,← pair_map sigma tau H hcomm hH]
    exact h _ ⟨x,hx,rfl⟩
  · rintro h x ⟨v,hv,rfl⟩
    change hermitianPair sigma H (coordinateEquiv tau v) (coordinateEquiv tau v) = 0
    rw [pair_map sigma tau H hcomm hH,h v hv,map_zero]

variable [Finite K]

def pointEquiv (hcomm : Function.Commute sigma tau) (hH : H.map tau = H) : Equiv.Perm (SingularPoint sigma H) :=
  Equiv.subtypeEquiv (Submodule.orderIsoMapComap (coordinateEquiv tau)).toEquiv (fun P => by
    change (Module.finrank K P = 1 ∧ ∀ x ∈ P, hermitianPair sigma H x x = 0) ↔
      (Module.finrank K (P.map (coordinateEquiv tau).toLinearMap) = 1 ∧
        ∀ x ∈ P.map (coordinateEquiv tau).toLinearMap, hermitianPair sigma H x x = 0)
    rw [CFSGFiniteFieldSemilinearDimension.finrank_map,singular_map_iff sigma tau H hcomm hH])

theorem point_orthogonality (P Q : SingularPoint sigma H) :
    Orthogonal sigma H (pointEquiv sigma tau H hcomm hH P).val
      (pointEquiv sigma tau H hcomm hH Q).val ↔ Orthogonal sigma H P.val Q.val := by
  constructor
  · intro h x hx y hy
    apply tau.injective
    rw [map_zero,← pair_map sigma tau H hcomm hH]
    exact h _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
  · rintro h x ⟨v,hv,rfl⟩ y ⟨w,hw,rfl⟩
    change hermitianPair sigma H (coordinateEquiv tau v) (coordinateEquiv tau w) = 0
    rw [pair_map sigma tau H hcomm hH,h v hv w hw,map_zero]

def normalizedPoints (f : Equiv.Perm (SingularPoint sigma H)) :
    Equiv.Perm (SingularPoint sigma H) :=
  f.trans (pointEquiv sigma tau H hcomm hH).symm

theorem normalized_orthogonality (f : Equiv.Perm (SingularPoint sigma H))
    (hf : PreservesOrthogonality sigma H f) :
    PreservesOrthogonality sigma H (normalizedPoints sigma tau H hcomm hH f) := by
  intro P Q
  have he := point_orthogonality sigma tau H hcomm hH
    ((pointEquiv sigma tau H hcomm hH).symm (f P))
    ((pointEquiv sigma tau H hcomm hH).symm (f Q))
  simp only [Equiv.apply_symm_apply] at he
  exact he.symm.trans (hf P Q)

end SymmetricSubgroupAsymptotics.CFSGHermitianFieldAction
