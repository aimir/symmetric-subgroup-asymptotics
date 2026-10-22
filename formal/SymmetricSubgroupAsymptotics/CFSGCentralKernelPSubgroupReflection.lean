import SymmetricSubgroupAsymptotics.CFSGCentralKernelPSubgroups
import SymmetricSubgroupAsymptotics.CFSGSubgroupConjugateRestriction
import SymmetricSubgroupAsymptotics.CFSGSubgroupConjugateOrbitCardinality

/-! Central-kernel separation of p-elements reflects the actual
inclusion and normalizer geometry of p-subgroups. Separate restriction
injectivity on two subgroups would not justify these conclusions. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGCentralKernelPSubgroupReflection
open CFSGCentralKernelPElements CFSGSubgroupConjugateRestriction
open CFSGSubgroupConjugateOrbitCardinality
variable {G H : Type*} [Group G] [Group H] {p : ℕ} [Fact p.Prime]
    (f : G→*H) (P : Sylow p G)
    (hP : Function.Injective (f.comp (P : Subgroup G).subtype))
    (hker : f.ker≤Subgroup.center G)

include f P hP hker

theorem map_le_map_iff (U V : Subgroup G) (hU : IsPGroup p U) (hV : IsPGroup p V) :
    U.map f≤V.map f↔U≤V := by
  constructor
  · intro h u hu
    obtain ⟨v,hv,he⟩ := h (show f u∈U.map f from ⟨u,hu,rfl⟩)
    obtain ⟨a,ha⟩ := hU ⟨u,hu⟩
    obtain ⟨b,hb⟩ := hV ⟨v,hv⟩
    have huv : u=v := eq_of_p_elements f P hP hker u v
      ⟨a,congrArg Subtype.val ha⟩ ⟨b,congrArg Subtype.val hb⟩ he.symm
    rw [huv]
    exact hv
  · exact Subgroup.map_mono

theorem mem_normalizer_map_iff (U : Subgroup G) (hU : IsPGroup p U) (g : G) :
    f g∈Subgroup.normalizer (U.map f : Set H)↔g∈Subgroup.normalizer (U : Set G) := by
  constructor
  · intro hg
    have he : (U.map (MulAut.conj g).toMonoidHom).map f=U.map f := by
      rw [map_conjugate]
      exact conjugate_eq_of_mem_normalizer (U.map f) (f g) hg
    have hconj : IsPGroup p (U.map (MulAut.conj g).toMonoidHom) := hU.map _
    have hleft := (map_le_map_iff f P hP hker _ U hconj hU).mp he.le
    have hright := (map_le_map_iff f P hP hker U _ hU hconj).mp he.symm.le
    apply Subgroup.mem_normalizer_iff_conj_image_eq.mpr
    exact congrArg (fun S : Subgroup G=>(S : Set G)) (le_antisymm hleft hright)
  · intro hg
    exact Subgroup.le_normalizer_map f (show f g∈(Subgroup.normalizer (U : Set G)).map f from
      ⟨g,hg,rfl⟩)

end SymmetricSubgroupAsymptotics.CFSGCentralKernelPSubgroupReflection
