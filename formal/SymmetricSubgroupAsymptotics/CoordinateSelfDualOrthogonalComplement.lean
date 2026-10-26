import SymmetricSubgroupAsymptotics.SignedMonomialCoordinateSelfDual
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The coordinate pairing gives the actual complementary-dimensional
invariant subspace for a self-dual action. This retains the SAME operators
and the genuine annihilator; no invariant complement is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CoordinateSelfDualOrthogonalComplement
open SignedMonomialCoordinateSelfDual LinearContragredientSmallSpaceAction

variable {K I : Type*} [Field K] [Fintype I]

def orthogonal (W : Submodule K (I → K)) : Submodule K (I → K) :=
  W.dualAnnihilator.comap (coordinateDualEquiv (I:=I) (K:=K)).toLinearMap

theorem finrank_add_orthogonal (W : Submodule K (I → K)) :
    Module.finrank K W+Module.finrank K (orthogonal W)=Fintype.card I := by
  have hdim : Module.finrank K (orthogonal W)=Module.finrank K W.dualAnnihilator :=
    ((coordinateDualEquiv (I:=I) (K:=K)).ofSubmodule' W.dualAnnihilator).finrank_eq
  calc
    _=Module.finrank K W+Module.finrank K W.dualAnnihilator :=
      congrArg (fun n : ℕ => Module.finrank K W+n) hdim
    _=Module.finrank K (I → K) := Subspace.finrank_add_finrank_dualAnnihilator_eq W
    _=Fintype.card I := Module.finrank_fintype_fun_eq_card K

theorem orthogonal_ne_bot_of_proper (W : Submodule K (I → K)) (hW : W≠⊤) :
    orthogonal W≠⊥ := by
  have hlt : Module.finrank K W<Fintype.card I := by
    simpa only [Module.finrank_fintype_fun_eq_card] using Submodule.finrank_lt hW
  have hdim := finrank_add_orthogonal W
  intro he
  rw [he,finrank_bot] at hdim
  omega

theorem invariant {G : Type*} [Group G]
    (ρ : G →* ((I → K) ≃ₗ[K] (I → K)))
    (hself : ∀ (g : G) (v : I → K),coordinateDualEquiv (ρ g v)=
      contragredient ρ g (coordinateDualEquiv v))
    (W : Submodule K (I → K))
    (hW : ∀ g w,w∈W → ρ g w∈W)
    (g : G) (v : I → K) (hv : v∈orthogonal W) :
    ρ g v∈orthogonal W := by
  change coordinateDualEquiv (ρ g v)∈W.dualAnnihilator
  rw [hself]
  apply (W.mem_dualAnnihilator _).mpr
  intro w hw
  change coordinateDualEquiv v ((ρ g).symm w)=0
  have hinv : (ρ g).symm=ρ g⁻¹ := by rw [ρ.map_inv]; rfl
  rw [hinv]
  exact (W.mem_dualAnnihilator (coordinateDualEquiv v)).mp hv _ (hW g⁻¹ w hw)

end SymmetricSubgroupAsymptotics.CoordinateSelfDualOrthogonalComplement
