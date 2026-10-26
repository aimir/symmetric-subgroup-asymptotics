import SymmetricSubgroupAsymptotics.LinearContragredientSmallSpaceAction

/-! Actual invariant hyperplanes are kernels of actual nonzero
functionals. An invariant line in dimension three supplies such a
hyperplane on the SAME contragredient representation. This retains
kernel invariance, not the stronger and generally false assertion that
the functional itself is fixed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.InvariantLinePlaneFunctionalChart
open LinearContragredientSmallSpaceAction
variable {K V G : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Group G]

theorem exists_functional_ker_eq_of_codimension_one (W : Submodule K V)
    (hdim : Module.finrank K W+1=Module.finrank K V) :
    ∃ ℓ : Module.Dual K V, ℓ≠0 ∧ ℓ.ker=W := by
  have hs := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  have hd : Module.finrank K W.dualAnnihilator=1 := by omega
  letI : Nontrivial W.dualAnnihilator := Module.finrank_pos_iff.mp (by rw [hd]; decide)
  obtain ⟨ℓ,hℓ⟩ := exists_ne (0 : W.dualAnnihilator)
  have hn : ℓ.val≠0 := by
    intro h
    apply hℓ
    exact Subtype.ext h
  obtain ⟨v,hv⟩ := DFunLike.ne_iff.mp hn
  have hsurj : Function.Surjective ℓ.val := by
    intro c
    refine ⟨(c/ℓ.val v) • v,?_⟩
    rw [map_smul,smul_eq_mul,div_mul_cancel₀ _ hv]
  have hker := ℓ.val.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj,finrank_top,CommSemiring.finrank_self] at hker
  have hle : W≤ℓ.val.ker := by
    intro w hw
    exact (Submodule.mem_dualAnnihilator ℓ.val).mp ℓ.property w hw
  have he : W=ℓ.val.ker := Submodule.eq_of_le_of_finrank_eq hle (by omega)
  exact ⟨ℓ.val,hn,he.symm⟩

theorem exists_invariant_kernel_functional_of_codimension_one
    (ρ : G →* (V ≃ₗ[K] V)) (W : Submodule K V)
    (hdim : Module.finrank K W+1=Module.finrank K V)
    (hW : ∀ (g : G) (v : V), v∈W → ρ g v∈W) :
    ∃ ℓ : Module.Dual K V, ℓ≠0 ∧
      ∀ (g : G) (v : V), ℓ (ρ g v)=0 ↔ ℓ v=0 := by
  obtain ⟨ℓ,hℓ,he⟩ := exists_functional_ker_eq_of_codimension_one W hdim
  refine ⟨ℓ,hℓ,?_⟩
  intro g v
  have hiff (w : V) : ℓ w=0 ↔ w∈W := by
    change w∈ℓ.ker ↔ w∈W
    rw [he]
  rw [hiff,hiff]
  constructor
  · intro hv
    have hh := hW g⁻¹ (ρ g v) hv
    rw [ρ.map_inv] at hh
    exact (ρ g).symm_apply_apply v ▸ hh
  · exact hW g v

theorem dualAnnihilator_invariant (ρ : G →* (V ≃ₗ[K] V)) (W : Submodule K V)
    (hW : ∀ (g : G) (v : V), v∈W → ρ g v∈W)
    (g : G) (ℓ : Module.Dual K V) (hℓ : ℓ∈W.dualAnnihilator) :
    contragredient ρ g ℓ∈W.dualAnnihilator := by
  apply (Submodule.mem_dualAnnihilator _).mpr
  intro v hv
  change ℓ ((ρ g).symm v)=0
  have hinv : (ρ g).symm=ρ g⁻¹ := by rw [ρ.map_inv]; rfl
  rw [hinv]
  exact (Submodule.mem_dualAnnihilator ℓ).mp hℓ _ (hW g⁻¹ v hv)

theorem exists_invariant_kernel_functional_on_dual_of_line_in_three
    (ρ : G →* (V ≃ₗ[K] V)) (W : Submodule K V)
    (hdim : Module.finrank K V=3) (hline : Module.finrank K W=1)
    (hW : ∀ (g : G) (v : V), v∈W → ρ g v∈W) :
    ∃ ℓ : Module.Dual K (Module.Dual K V), ℓ≠0 ∧
      ∀ (g : G) (v : Module.Dual K V),
        ℓ (contragredient ρ g v)=0 ↔ ℓ v=0 := by
  have hs := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  have hdual : Module.finrank K (Module.Dual K V)=3 :=
    Subspace.dual_finrank_eq.trans hdim
  apply exists_invariant_kernel_functional_of_codimension_one
    (contragredient ρ) W.dualAnnihilator (by omega)
  exact dualAnnihilator_invariant ρ W hW

end SymmetricSubgroupAsymptotics.InvariantLinePlaneFunctionalChart
