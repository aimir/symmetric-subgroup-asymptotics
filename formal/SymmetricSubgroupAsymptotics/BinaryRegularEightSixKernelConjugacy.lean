import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryHeads
import SymmetricSubgroupAsymptotics.BinaryPairFrameKernelTransport
import SymmetricSubgroupAsymptotics.BinaryPairFrameConjugateTop

/-! Seven explicit normalizer permutations carry the seven original
six-dimensional regular-eight kernel charts to chart24. Only these seven
permutations, their action on three generators, and six-vector bases are
checked; no normalizer or group-action enumeration is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryRegularEightSixKernelConjugacy
open BinaryRegularEightNaturalRegistry

def index : Fin 7 → Fin 47 := ![24,25,26,28,29,31,32]
def sourceChart : Fin 7 → BinaryCoordinateSpace 8 6 :=
  ![chart24,chart25,chart26,chart28,chart29,chart31,chart32]

def forward : Fin 7 → Fin 8 → Fin 8 :=
  ![![0,1,2,3,4,5,6,7], ![0,1,6,7,4,5,2,3], ![0,7,4,5,2,1,6,3],
    ![0,5,2,7,4,1,6,3], ![0,6,2,3,7,5,1,4], ![0,3,4,1,2,5,6,7], ![0,5,6,3,4,1,2,7]]

def backward : Fin 7 → Fin 8 → Fin 8 :=
  ![![0,1,2,3,4,5,6,7], ![0,1,6,7,4,5,2,3], ![0,5,4,7,2,3,6,1],
    ![0,5,2,7,4,1,6,3], ![0,6,2,3,7,5,1,4], ![0,3,4,1,2,5,6,7], ![0,5,6,3,4,1,2,7]]

private theorem left_inverse : ∀ (c : Fin 7) (x : Fin 8), backward c (forward c x)=x := by
  decide +kernel
private theorem right_inverse : ∀ (c : Fin 7) (x : Fin 8), forward c (backward c x)=x := by
  decide +kernel

def conjugator (c : Fin 7) : Equiv.Perm (Fin 8) where
  toFun := forward c
  invFun := backward c
  left_inv := left_inverse c
  right_inv := right_inverse c

def reindex (p : Equiv.Perm (Fin 8)) : V ≃ₗ[ZMod 2] V where
  toFun v := fun x => v (p.symm x)
  invFun v := fun x => v (p x)
  left_inv v := by funext x; exact congrArg v (p.symm_apply_apply x)
  right_inv v := by funext x; exact congrArg v (p.apply_symm_apply x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem chart_basis_transport : ∀ (c : Fin 7) (b : Fin 6),
    reindex (conjugator c) ((sourceChart c).inclusion (Pi.single b 1)) ∈ chart24.space := by
  simp only [BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem forward_generator_words : ∀ (c : Fin 7) (j : Fin 3), ∃ k : Fin 8,
    (MulAut.conj (conjugator c)) (BinaryMenuCayley8T3.generators j)=(groupElement k).val := by
  decide +kernel
private theorem backward_generator_words : ∀ (c : Fin 7) (j : Fin 3), ∃ k : Fin 8,
    (MulAut.conj (conjugator c)⁻¹) (BinaryMenuCayley8T3.generators j)=(groupElement k).val := by
  decide +kernel

theorem conjugator_normalizes (c : Fin 7) :
    H.map (MulAut.conj (conjugator c)).toMonoidHom=H := by
  have hf : H.map (MulAut.conj (conjugator c)).toMonoidHom≤H := by
    apply Subgroup.map_le_iff_le_comap.mpr
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    change (MulAut.conj (conjugator c)) (BinaryMenuCayley8T3.generators j)∈H
    obtain ⟨k,hk⟩ := forward_generator_words c j
    rw [hk]
    exact (groupElement k).property
  have hb : H.map (MulAut.conj (conjugator c)⁻¹).toMonoidHom≤H := by
    apply Subgroup.map_le_iff_le_comap.mpr
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    change (MulAut.conj (conjugator c)⁻¹) (BinaryMenuCayley8T3.generators j)∈H
    obtain ⟨k,hk⟩ := backward_generator_words c j
    rw [hk]
    exact (groupElement k).property
  apply le_antisymm hf
  intro g hg
  have hz : (MulAut.conj (conjugator c)⁻¹) g∈H := hb ⟨g,hg,rfl⟩
  refine ⟨(MulAut.conj (conjugator c)⁻¹) g,hz,?_⟩
  change conjugator c*((conjugator c)⁻¹*g*conjugator c)*(conjugator c)⁻¹=g
  group

theorem chart_transport (c : Fin 7) :
    (sourceChart c).space.map (reindex (conjugator c)).toLinearMap=chart24.space := by
  have hle : (sourceChart c).space.map (reindex (conjugator c)).toLinearMap≤chart24.space := by
    apply Submodule.map_le_iff_le_comap.mpr
    exact (sourceChart c).le_of_basis_mem _ (chart_basis_transport c)
  have hd : Module.finrank (ZMod 2) ((sourceChart c).space.map
      (reindex (conjugator c)).toLinearMap)=6 := by
    rw [← ((reindex (conjugator c)).submoduleMap (sourceChart c).space).finrank_eq]
    exact (sourceChart c).finrank
  exact Submodule.eq_of_le_of_finrank_eq hle (hd.trans chart24.finrank.symm)

theorem sourceChart_space (c : Fin 7) : (sourceChart c).space=(charts (index c)).2.space := by
  fin_cases c <;> rfl

private theorem six_indices : ∀ i : Fin 47, (charts i).1=6 → ∃ c : Fin 7,index c=i := by
  decide +kernel

theorem six_dimensional_state_conjugate (K : Subrepresentation rho)
    (hK : Module.finrank (ZMod 2) K.toSubmodule=6) :
    ∃ c : Fin 7,K.toSubmodule.map (reindex (conjugator c)).toLinearMap=chart24.space := by
  obtain ⟨i,rfl⟩ := complete K
  rw [states_space,(charts i).2.finrank] at hK
  obtain ⟨c,hc⟩ := six_indices i hK
  refine ⟨c,?_⟩
  rw [states_space,←hc,←sourceChart_space]
  exact chart_transport c

end SymmetricSubgroupAsymptotics.BinaryRegularEightSixKernelConjugacy
