import SymmetricSubgroupAsymptotics.CFSGSuzukiSubgroupPrimeFieldLayers
import SymmetricSubgroupAsymptotics.ScalarDualAnnihilatorOrbitIndex
import SymmetricSubgroupAsymptotics.CentralExtensionSemidirectStabilizer
import SymmetricSubgroupAsymptotics.ScalarAffineLineGroup

/-! Central annihilator coupling for the SAME actual subgroup M of
Suzuki U semidirect T. Inner U conjugation is removed only on its actual
central subgroup. No assertion that naked projected T preserves J is
made, and no extra prime multiplier is introduced. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiCentralAnnihilatorIndex
open CFSGSuzukiFieldParameters CFSGSuzukiUnipotent CFSGSuzukiCentralExtensionLayers
open CFSGSuzukiSubgroupPrimeFieldLayers

abbrev Borel (m : ℕ) := unipotentSubgroup m ⋊[torusAutHom m] (Field m)ˣ

def centralGroupAction (m : ℕ) : (Field m)ˣ →* MulAut (Multiplicative (Field m)) :=
  (ScalarAffineLineGroup.scalarAction (Field m)).comp (centralWeight m)

def centralLinearAction (m : ℕ) : (Field m)ˣ →* (Field m ≃ₗ[ZMod 2] Field m) :=
  ScalarDualAnnihilatorOrbitIndex.scalarAction (F := ZMod 2) (centralWeight m)

theorem centralSubspace_stable (m : ℕ) (M : Subgroup (Borel m)) (t : (Field m)ˣ)
    (ht : t ∈ M.map SemidirectProduct.rightHom) (x : Field m)
    (hx : x ∈ centralSubspace m (M.comap SemidirectProduct.inl)) :
    centralLinearAction m t x ∈ centralSubspace m (M.comap SemidirectProduct.inl) := by
  have h := CentralExtensionSemidirectStabilizer.central_action_mem_of_projected
    (torusAutHom m) (centralHom m) (centralGroupAction m)
    (fun c z => centralHom_torus m c z) (centralHom_mem_center m)
    M t ht (Multiplicative.ofAdd x) hx
  exact h

theorem central_quotient_mul_projected_index_ge (m : ℕ) (M : Subgroup (Borel m))
    (hM : ¬(centralHom m).range ≤ M.comap SemidirectProduct.inl) :
    Nat.card (Field m) - 1 ≤
      Nat.card ((Field m) ⧸ centralSubspace m (M.comap SemidirectProduct.inl)) *
        (M.map SemidirectProduct.rightHom).index := by
  let C := centralSubspace m (M.comap SemidirectProduct.inl)
  have hC : C ≠ ⊤ := centralSubspace_ne_top m _ hM
  have hz : ∃ z : Field m, z ∉ C := by
    by_contra h
    apply hC
    apply top_unique
    intro z _
    exact not_not.mp (not_exists.mp h z)
  obtain ⟨z, hz⟩ := hz
  obtain ⟨f, hf⟩ := InvariantAnnihilatorOrbitIndex.exists_annihilator_nonzero_on C z hz
  have hf0 : f.val ≠ 0 := by
    intro he
    apply hf
    rw [he, LinearMap.zero_apply]
  exact ScalarDualAnnihilatorOrbitIndex.quotient_card_mul_index_ge (F := ZMod 2)
    (centralWeight m) (centralWeight_surjective m)
    (M.map SemidirectProduct.rightHom) C (centralSubspace_stable m M) f hf0

theorem index_mul_actual_layer_cards (m : ℕ) (M : Subgroup (Borel m)) :
    M.index * Nat.card (centralSubspace m (M.comap SemidirectProduct.inl)) *
        Nat.card (vectorSubspace m (M.comap SemidirectProduct.inl)) =
      Nat.card (Field m) * Nat.card (Field m) * (M.map SemidirectProduct.rightHom).index := by
  have h := CentralExtensionSemidirectStabilizer.index_mul_layer_cards (torusAutHom m)
    (firstParameterHom m) (firstParameterHom_surjective m) (centralHom m) (centralHom_range m) M
  rw [← centralSubspace_card m (M.comap SemidirectProduct.inl),
    ← vectorSubspace_card m (M.comap SemidirectProduct.inl)] at h
  exact h

end SymmetricSubgroupAsymptotics.CFSGSuzukiCentralAnnihilatorIndex
