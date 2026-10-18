import SymmetricSubgroupAsymptotics.BinaryPairInvariantAxes
import SymmetricSubgroupAsymptotics.BinaryFourRegularFixedLine
import SymmetricSubgroupAsymptotics.MonolithicSelfCentralizingKernelNormalCover

/-! The literal constant flip is a monolith of an actual four-pair frame.
The top is always the original pair-action range. No identification with
A4/S4, full flip module, or augmentation module is assumed. -/

set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 4))

/-- Separating flip coordinates make the actual elementary kernel
self-centralizing. Three augmentation flips already suffice. -/
theorem kernel_selfCentralizing_of_bits_separate
    (hsep : ∀ i j : Fin 4, i ≠ j →
      ∃ k : F.top.ker, F.bits k i ≠ F.bits k j) :
    Subgroup.centralizer (F.top.ker : Set U) ≤ F.top.ker := by
  intro g hg
  have hcomm := Subgroup.mem_centralizer_iff.mp hg
  have hbits : ∀ (k : F.top.ker) i,
      F.bits k ((F.top g)⁻¹ i) = F.bits k i := by
    intro k i
    have hk : MulAut.conjNormal g k = k := by
      apply Subtype.ext
      change g * (k : U) * g⁻¹ = (k : U)
      rw [← hcomm (k : U) k.property]
      exact mul_inv_cancel_right _ _
    rw [← F.bits_conjNormal, hk]
  have hinv : ∀ i : Fin 4, (F.top g)⁻¹ i = i := by
    intro i
    by_contra hne
    obtain ⟨k, hk⟩ := hsep _ _ hne
    exact hk (hbits k i)
  change F.top g = 1
  apply Equiv.ext
  intro i
  have hh := hinv (F.top g i)
  simpa only [Equiv.Perm.inv_def, Equiv.symm_apply_apply, Equiv.Perm.one_apply] using hh.symm

/-- Small coordinate inputs imply a cover of every nontrivial original
normal subgroup by the actual constant-flip element. In particular the
regular Klein group P is a normal subgroup of the actual pair-top range. -/
theorem constantFlip_mem_every_nontrivial_normal
    (P : Subgroup F.top.range) [P.Normal] (hP : IsPGroup 2 P)
    (u v : P)
    (hu : ∀ x i, F.coordinateTopAction u x i = x (![1, 0, 3, 2] i))
    (hv : ∀ x i, F.coordinateTopAction v x i = x (![2, 3, 0, 1] i))
    (c : F.top.ker) (hc : ∀ i, F.bits c i = 1)
    (hsep : ∀ i j : Fin 4, i ≠ j →
      ∃ k : F.top.ker, F.bits k i ≠ F.bits k j)
    (N : Subgroup U) (hN : N.Normal) (hne : N ≠ ⊥) : (c : U) ∈ N := by
  have hconstant : ∀ t : P, F.coordinateTopAction t (fun _ => 1) = fun _ => 1 := by
    intro t
    funext i
    rfl
  let D : Subgroup U := Subgroup.zpowers (c : U)
  have hcover : D ≤ N := by
    apply normal_cover_of_selfCentralizing_monolith F.top.ker D
      (F.kernel_selfCentralizing_of_bits_separate hsep) ?_ N hN hne
    intro H hH hHker hHne
    letI : H.Normal := hH
    have haxis : F.axisSubrepresentation H ≠ ⊥ := by
      intro hzero
      apply hHne
      apply le_antisymm _ bot_le
      intro g hg
      let k : F.top.ker := ⟨g, hHker hg⟩
      have hm : F.bits k ∈ F.axisSubrepresentation H :=
        (F.bits_mem_ambientAxis H k).mpr hg
      rw [hzero] at hm
      have hk : k = 1 := by
        apply F.bitsHom_injective
        apply Multiplicative.toAdd.injective
        change F.bits k = (F.bitsHom 1).toAdd
        rw [map_one]
        exact hm
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val hk)
    have hatom : IsAtom (NormalPMonolithicCommutator.fixed F.coordinateTopAction P) :=
      BinaryFourRegularFixedLine.fixed_isAtom F.coordinateTopAction P
        (LinearMap.id) (fun _ _ h => h) u v hu hv (fun _ => 1) hconstant (fun _ => rfl)
    have hfixed := NormalPMonolithicCommutator.fixed_le_of_ne_bot
      F.coordinateTopAction P hP hatom (F.axisSubrepresentation H) haxis
    have hcmem : F.bits c ∈ F.axisSubrepresentation H := by
      apply hfixed
      have heq : F.bits c = fun _ => 1 := funext hc
      rw [heq]
      exact hconstant
    apply Subgroup.zpowers_le.mpr
    exact (F.bits_mem_ambientAxis H c).mp hcmem
  exact hcover (Subgroup.mem_zpowers (c : U))

end SymmetricSubgroupAsymptotics.BinaryPairFrame

end
