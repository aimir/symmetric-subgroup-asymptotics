import SymmetricSubgroupAsymptotics.BinaryQuadraticRefinementAction
import SymmetricSubgroupAsymptotics.BilinearNaturalDualOrbitTransfer

/-! A preserved nondegenerate form identifies the actual natural action
and its contragredient. In particular their point stabilizers coincide
inside the SAME group, and nonzero-vector transitivity transfers to the
dual. This assumes no class-count bound. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BilinearContragredientDuality
open BinaryQuadraticRefinementAction

variable {G K V : Type*} [Group G] [Field K] [AddCommGroup V] [Module K V]

abbrev naturalAction (ρ : G →* (V ≃ₗ[K] V)) : MulAction G V where
  smul g v := ρ g v
  one_smul v := by
    change ρ (1 : G) v = v
    rw [map_one]
    rfl
  mul_smul g h v := by
    change ρ (g*h) v = ρ g (ρ h v)
    rw [map_mul]
    rfl

variable [Module.Finite K V] (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (ρ : G →* (V ≃ₗ[K] V))
    (hρ : ∀ g : G, ∀ x y : V, B (ρ g x) (ρ g y) = B x y)

include B hB hρ

theorem toDual_equivariant (g : G) (v : V) :
    letI := dualAction ρ
    B.toDual hB (ρ g v) = g • B.toDual hB v :=
  BilinearNaturalDualOrbitTransfer.bilinear_covariance B ρ hρ g v

theorem fixed_toDual_iff (g : G) (v : V) :
    letI := dualAction ρ
    g • B.toDual hB v = B.toDual hB v ↔ ρ g v = v := by
  letI := dualAction ρ
  rw [← toDual_equivariant B hB ρ hρ]
  exact (B.toDual hB).injective.eq_iff

theorem stabilizer_toDual_eq (v : V) :
    letI := naturalAction ρ
    letI := dualAction ρ
    MulAction.stabilizer G (B.toDual hB v) = MulAction.stabilizer G v := by
  letI := naturalAction ρ
  letI := dualAction ρ
  ext g
  exact fixed_toDual_iff B hB ρ hρ g v

theorem dual_nonzero_transitive
    (htrans : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ g : G, ρ g v = w)
    (f₀ f : Module.Dual K V) (hf₀ : f₀ ≠ 0) (hf : f ≠ 0) :
    letI := dualAction ρ
    ∃ g : G, g • f₀ = f := by
  letI := dualAction ρ
  let e := B.toDual hB
  have hv₀ : e.symm f₀ ≠ 0 := by
    intro h
    apply hf₀
    have he := congrArg e h
    simpa only [e.apply_symm_apply, map_zero] using he
  have hv : e.symm f ≠ 0 := by
    intro h
    apply hf
    have he := congrArg e h
    simpa only [e.apply_symm_apply, map_zero] using he
  obtain ⟨g, hg⟩ := htrans (e.symm f₀) (e.symm f) hv₀ hv
  refine ⟨g, ?_⟩
  have he := toDual_equivariant B hB ρ hρ g (e.symm f₀)
  change e (ρ g (e.symm f₀)) = g • e (e.symm f₀) at he
  rw [hg, e.apply_symm_apply, e.apply_symm_apply] at he
  exact he.symm

end SymmetricSubgroupAsymptotics.BilinearContragredientDuality
