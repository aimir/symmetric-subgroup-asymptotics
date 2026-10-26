import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.GroupTheory.Subgroup.Centralizer

/-! A central kernel cannot survive when a self-normalizing subgroup
already sees the homomorphism injectively. No ambient simplicity,
subgroup recognition, order formula, or trivial-kernel premise is used. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CentralKernelSelfNormalizerInjectivity

theorem injective {G H : Type*} [Group G] [Group H]
    (f : G→*H) (P : Subgroup G)
    (hP : Function.Injective (f.comp P.subtype))
    (hker : f.ker≤Subgroup.center G)
    (hN : Subgroup.normalizer (P : Set G)=P) : Function.Injective f := by
  apply f.ker_eq_bot_iff.mp
  apply le_antisymm _ bot_le
  intro z hz
  have hzN : z∈Subgroup.normalizer (P : Set G) :=
    (hker.trans (Subgroup.center_le_normalizer (P : Set G))) hz
  have hzP : z∈P := Eq.mp (congrArg (fun S : Subgroup G=>z∈S) hN) hzN
  have hm : f z=f 1 := (MonoidHom.mem_ker.mp hz).trans (map_one f).symm
  have he : (⟨z,hzP⟩ : P)=1 := hP hm
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val he)

end SymmetricSubgroupAsymptotics.CentralKernelSelfNormalizerInjectivity
