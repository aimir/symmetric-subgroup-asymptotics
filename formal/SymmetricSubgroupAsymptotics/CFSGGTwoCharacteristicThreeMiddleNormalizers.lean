import SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleCoordinateEquiv
import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalSimpleWeylTransport
import Mathlib.GroupTheory.Subgroup.Centralizer

/-! Genuine short-root and Weyl normalizers of the literal ordinary
middle complement. Root transport proves Weyl normalization; no SL2
recognition or ambient linear normalizer is substituted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleNormalizers
open CFSG.Models.Chevalley CFSGGTwoOriginalPositiveRootWords
open CFSGGTwoPositiveSixWord CFSGGTwoPositiveWordSubgroup CFSGGTwoPositiveCoordinateKernels
open CFSGGTwoCharacteristicThreeMiddleFiveCoordinates
open CFSGGTwoCharacteristicThreeMiddleCoordinateEquiv
open CFSGGTwoOriginalSimpleWeylTransport
open CFSGGTwoOriginalPositiveCollecting
variable (K : Type) [Field K] [CharP K 3]

theorem positive_root_mem_middle (j : Fin 6) (hj : j ≠ 0) (a : K) :
    positiveModel K j a ∈ Middle K := by
  apply (mem_complement_iff K 0 _).mpr
  refine ⟨Pi.single j a,modelWord_single K j a,?_⟩
  change (Pi.single j a : Fin 6 → K) (0 : Fin 6) = 0
  simp only [Pi.single_apply,Ne.symm hj,if_false]

theorem middleWord_factors (v : Fin 5 → K) :
    middleWord K v = positiveModel K 1 (v 0)*positiveModel K 2 (v 1)*
      positiveModel K 3 (v 2)*positiveModel K 4 (v 3)*positiveModel K 5 (v 4) := by
  change positiveModel K 0 0*positiveModel K 1 (v 0)*positiveModel K 2 (v 1)*
      positiveModel K 3 (v 2)*positiveModel K 4 (v 3)*positiveModel K 5 (v 4) = _
  rw [positiveModel_zero,one_mul]

theorem positive_le_normalizer_middle : positiveWordGroup K ≤
    Subgroup.normalizer (Middle K : Set (Model CartanMatrix.G₂ K)) := by
  intro u hu
  let S := (coordinateHom K 0).ker
  have hn : (⟨u,hu⟩ : positiveWordGroup K) ∈ Subgroup.normalizer S := by
    rw [Subgroup.normalizer_eq_top]
    trivial
  exact (Subgroup.le_normalizer_map (H := S) (positiveWordGroup K).subtype) ⟨⟨u,hu⟩,hn,rfl⟩

theorem shortWeyl_normalizes_middle [Finite K] : shortWord K ∈
    Subgroup.normalizer (Middle K : Set (Model CartanMatrix.G₂ K)) := by
  letI : Finite (Middle K) := Finite.of_equiv (Fin 5 → K) (coordinateEquiv K)
  have hle : (Middle K).map (MulAut.conj (shortWord K)).toMonoidHom ≤ Middle K := by
    rintro x ⟨u,hu,rfl⟩
    obtain ⟨v,rfl⟩ := (mem_complement_iff_middleWord K u).mp hu
    let c : MulAut (Model CartanMatrix.G₂ K) := MulAut.conj (shortWord K)
    have hc (j : Fin 6) (a : K) : c (positiveModel K j a) = shortImage K j a :=
      short_transport K j a
    change c (middleWord K v) ∈ Middle K
    rw [middleWord_factors]
    simp only [map_mul,hc,shortImage]
    exact (Middle K).mul_mem ((Middle K).mul_mem ((Middle K).mul_mem
      ((Middle K).mul_mem (positive_root_mem_middle K 4 (by decide) _)
        (positive_root_mem_middle K 3 (by decide) _))
      (positive_root_mem_middle K 2 (by decide) _))
      (positive_root_mem_middle K 1 (by decide) _))
      (positive_root_mem_middle K 5 (by decide) _)
  have he : (Middle K).map (MulAut.conj (shortWord K)).toMonoidHom = Middle K :=
    Subgroup.eq_of_le_of_card_ge hle
      (Nat.card_congr ((MulAut.conj (shortWord K)).subgroupMap (Middle K)).toEquiv).le
  exact Subgroup.mem_normalizer_iff_conj_image_eq.mpr
    (congrArg (fun H : Subgroup (Model CartanMatrix.G₂ K) =>
      (H : Set (Model CartanMatrix.G₂ K))) he)

end SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleNormalizers
