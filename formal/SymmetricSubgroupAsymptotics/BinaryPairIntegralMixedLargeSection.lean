import SymmetricSubgroupAsymptotics.BinaryPairLargeSectionCharacter
import Mathlib.GroupTheory.Commutator.Basic

/-! A large original binary section detects mixed commutators from every
nontrivial actual top image. The denominator is the full integral
commutator intersection, with no reduction modulo two. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X I : Type} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U I)

/-- If all actual mixed commutators lie in L, the original E acts
trivially on the original section K/(K∩L). -/
theorem sectionTop_trivial_on_normal_of_commutator_intersection_le
    (E L : Subgroup U) [E.Normal] [L.Normal]
    (hcut : ⁅E, (⊤ : Subgroup U)⁆ ⊓ F.top.ker ≤ L)
    (e : U) (he : e ∈ E) :
    (F.sectionRepresentation L).comp (F.sectionTopQuotient L)
      (F.top.rangeRestrict e) = 1 := by
  have hm (k : F.top.ker) :
      F.sectionMap L (MulAut.conjNormal e k) = F.sectionMap L k := by
    let d : F.top.ker := k⁻¹ * MulAut.conjNormal e k
    have hc : (d : U) ∈ ⁅E, (⊤ : Subgroup U)⁆ := by
      have hc0 := Subgroup.commutator_mem_commutator
        (Subgroup.mem_top ((k : U)⁻¹)) he
      rw [Subgroup.commutator_comm] at hc0
      change (k : U)⁻¹ * e * (k : U) * e⁻¹ ∈ ⁅E, (⊤ : Subgroup U)⁆ at hc0
      change (k : U)⁻¹ * (e * (k : U) * e⁻¹) ∈ ⁅E, (⊤ : Subgroup U)⁆
      simpa only [mul_assoc] using hc0
    have hd : d ∈ (F.sectionMap L).ker := by
      rw [F.sectionMap_ker L]
      exact hcut ⟨hc, d.property⟩
    have hd1 : F.sectionMap L (k⁻¹ * MulAut.conjNormal e k) = 1 := hd
    symm
    simpa only [map_mul, map_inv, inv_mul_eq_one] using hd1
  apply DFunLike.ext
  intro v
  obtain ⟨k, hk⟩ := F.sectionMap_surjective L (Multiplicative.ofAdd v)
  have hv : (F.sectionMap L k).toAdd = v := congrArg Multiplicative.toAdd hk
  change F.sectionRepresentation L (F.sectionTopQuotient L (F.top.rangeRestrict e)) v = v
  rw [← hv, F.sectionTopQuotient_apply, F.sectionRepresentation_apply]
  exact congrArg Multiplicative.toAdd (hm k)

/-- A faithful large section forces every such normal subgroup to have
zero actual top image. -/
theorem normal_le_kernel_of_large_section_and_commutator_cut
    [Finite X] [Finite I] [MulAction.IsPretransitive F.top.range I]
    (hU : IsPGroup 2 U) (i : I)
    (E L : Subgroup U) [E.Normal] [L.Normal]
    (hlarge : Nat.card I < 2 * Module.finrank (ZMod 2)
      (F.kernelSpace ⧸ F.normalSpace L))
    (hcut : ⁅E, (⊤ : Subgroup U)⁆ ⊓ F.top.ker ≤ L) : E ≤ F.top.ker := by
  intro e he
  have ht : F.top.rangeRestrict e = 1 := by
    apply F.sectionTop_injective_of_large L hU i hlarge
    simpa only [map_one] using
      F.sectionTop_trivial_on_normal_of_commutator_intersection_le E L hcut e he
  exact congrArg Subtype.val ht

/-- In particular, a nonzero original top image contributes a genuine
extra mixed commutator outside any specified large-section cut. -/
theorem commutator_intersection_not_le_of_large_section
    [Finite X] [Finite I] [MulAction.IsPretransitive F.top.range I]
    (hU : IsPGroup 2 U) (i : I)
    (E L : Subgroup U) [E.Normal] [L.Normal]
    (hlarge : Nat.card I < 2 * Module.finrank (ZMod 2)
      (F.kernelSpace ⧸ F.normalSpace L))
    (hE : ¬ E ≤ F.top.ker) :
    ¬ ⁅E, (⊤ : Subgroup U)⁆ ⊓ F.top.ker ≤ L := by
  intro hcut
  exact hE (F.normal_le_kernel_of_large_section_and_commutator_cut hU i E L hlarge hcut)

end SymmetricSubgroupAsymptotics.BinaryPairFrame
