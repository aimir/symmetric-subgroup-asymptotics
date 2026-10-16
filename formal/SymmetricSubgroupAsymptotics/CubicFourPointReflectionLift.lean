import SymmetricSubgroupAsymptotics.SylowActualNormalizerLift
import SymmetricSubgroupAsymptotics.NormalizerKernelCentralizes
import SymmetricSubgroupAsymptotics.BinaryFourCubicNormalizerPointShapes

/-! A reflection in the actual four-block image lifts to an involution
when the original kernel has no Sylow-centralizing element. The lift
retains the actual Sylow subgroup and actual group elements. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CubicFourPointReflectionLift
open BinaryFourCubicNormalizerPointShapes

local instance reflectionLiftPrimeThree : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem exists_lift {G : Type} [Group G] [Finite G]
    (f : G →* Equiv.Perm (Fin 4)) (hf : Function.Surjective f)
    (S : Sylow 3 G) (s : G) (hgen : (S : Subgroup G) = Subgroup.zpowers s)
    (hfs : f s = blockCycle)
    (hinj : Function.Injective (f.comp (S : Subgroup G).subtype))
    (hzero : ∀ e : G, e ∈ f.ker →
      (∀ t : G, t ∈ (S : Subgroup G) → e*t = t*e) → e = 1) :
    ∃ g : G, g ∈ Subgroup.normalizer (S : Set G) ∧
      f g = Equiv.swap 2 3 ∧ g^2 = 1 ∧ g*s*g⁻¹ = s⁻¹ := by
  let r : Equiv.Perm (Fin 4) := Equiv.swap 2 3
  have hr2 : r^2 = 1 := by decide +kernel
  have hrconj : r*blockCycle*r⁻¹ = blockCycle⁻¹ := by decide +kernel
  have himage : (S : Subgroup G).map f = Subgroup.zpowers blockCycle := by
    rw [hgen,MonoidHom.map_zpowers,hfs]
  have hrnorm : r ∈ Subgroup.normalizer
      ((S : Subgroup G).map f : Set (Equiv.Perm (Fin 4))) := by
    rw [himage]
    apply Subgroup.mem_normalizer_iff_conj_image_eq.mpr
    change ((Subgroup.zpowers blockCycle).map (MulAut.conj r).toMonoidHom :
      Set (Equiv.Perm (Fin 4))) = _
    rw [MonoidHom.map_zpowers]
    change (Subgroup.zpowers (r*blockCycle*r⁻¹) : Set (Equiv.Perm (Fin 4))) = _
    rw [hrconj,Subgroup.zpowers_inv]
  obtain ⟨g,hgn,hfg⟩ := SylowActualNormalizerLift.exists_lift f hf S r hrnorm
  have hfixed : ∀ e : G, e ∈ f.ker →
      e ∈ Subgroup.normalizer (S : Set G) → e = 1 := by
    intro e he hen
    apply hzero e he
    intro t ht
    have h := NormalizerKernelCentralizes.conjugate_eq f (S : Subgroup G)
      hinj e he hen t ht
    exact (mul_inv_eq_iff_eq_mul).mp h
  have hg2 : g^2 = 1 := NormalizerKernelCentralizes.normalizing_square_eq_one
    f (S : Subgroup G) hfixed g hgn (by rw [hfg]; exact hr2)
  have hs : s ∈ (S : Subgroup G) := by
    rw [hgen]
    exact Subgroup.mem_zpowers s
  have hgs : g*s*g⁻¹ ∈ (S : Subgroup G) := (hgn s).mp hs
  have hsi : s⁻¹ ∈ (S : Subgroup G) := (S : Subgroup G).inv_mem hs
  have heq : (⟨g*s*g⁻¹,hgs⟩ : S) = ⟨s⁻¹,hsi⟩ := by
    apply hinj
    change f (g*s*g⁻¹) = f (s⁻¹)
    simp only [map_mul,map_inv,hfg,hfs]
    exact hrconj
  exact ⟨g,hgn,hfg,hg2,congrArg Subtype.val heq⟩

end SymmetricSubgroupAsymptotics.CubicFourPointReflectionLift
