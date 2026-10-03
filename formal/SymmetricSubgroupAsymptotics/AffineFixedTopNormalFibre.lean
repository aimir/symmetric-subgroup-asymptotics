import SymmetricSubgroupAsymptotics.ImageKernelSubgroupFibres
import SymmetricSubgroupAsymptotics.KernelCocycleGeneratorBound
import SymmetricSubgroupAsymptotics.OriginalKernelNormalSubrepresentation
import SymmetricSubgroupAsymptotics.JointElementaryLayerEnvelope

/-!
# Normal-axis fibres over one affine top axis

The fixed-top regrouping in `JointElementaryLayerEnvelope` needs a bound on
the original normal subgroups above one retained top.  We first forget
normality and identify the larger exact image/kernel-intersection fibre with
literal sections.  Once one section exists, its whole fibre is a torsor for
kernel cocycles and is therefore controlled by any generating tuple of the
retained top.  The invariant intersection is still the exact
`normalSubrepresentation` of the original kernel chart.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics

/-- A finite map with fibres of size at most `C` has total size at most the
size of its codomain times `C`. -/
theorem natCard_le_mul_of_fibre_le
    {X Y : Type*} [Finite X] [Finite Y]
    (f : X → Y) (C : ℕ)
    (h : ∀ y, Nat.card {x : X // f x = y} ≤ C) :
    Nat.card X ≤ Nat.card Y * C := by
  letI := Fintype.ofFinite X
  letI := Fintype.ofFinite Y
  calc
    Nat.card X = Fintype.card (Σ y : Y, {x : X // f x = y}) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_congr
        (Equiv.sigmaFiberEquiv f).symm]
    _ = ∑ y : Y, Fintype.card {x : X // f x = y} := Fintype.card_sigma
    _ ≤ ∑ _y : Y, C := Finset.sum_le_sum (fun y _ ↦ by
      simpa only [Nat.card_eq_fintype_card] using h y)
    _ = Nat.card Y * C := by
      simp [Nat.card_eq_fintype_card]

variable {G B : Type} [Group G] [Finite G] [Group B] [Finite B]

/-- Exact image/kernel subgroup fibres are bounded by the kernel raised to
the length of a generating tuple of the literal image.  Empty fibres are
included, and no normality condition is used in this enlargement. -/
theorem fixedImageKernelSubgroupFibre_card_le_generator_power
    (pi : G →* B) (D : Subgroup B) (I : Subgroup G)
    (hI : I ≤ pi.ker) [(I.subgroupOf (D.comap pi)).Normal]
    (d : ℕ) (generators : Fin d → D)
    (hgen : Subgroup.closure (Set.range generators) = ⊤) :
    Nat.card (FixedImageKernelSubgroupFibre pi D I) ≤
      Nat.card
        (QuotientGroup.lift (I.subgroupOf (D.comap pi))
          (pi.subgroupComap D)
          (imageKernel_le_restrictedKernel pi D I hI)).ker ^ d := by
  classical
  by_cases hnonempty : Nonempty (FixedImageKernelSubgroupFibre pi D I)
  · let H₀ : FixedImageKernelSubgroupFibre pi D I := Classical.choice hnonempty
    let s₀ := fixedImageKernelLiftEquiv pi D I hI H₀
    rw [Nat.card_congr (fixedImageKernelLiftEquiv pi D I hI),
      Nat.card_congr
        (homomorphicLiftEquivCocycle
          (QuotientGroup.lift (I.subgroupOf (D.comap pi))
            (pi.subgroupComap D)
            (imageKernel_le_restrictedKernel pi D I hI))
          (MonoidHom.id D) s₀)]
    exact kernelCocycle_card_le_generator_power
      (QuotientGroup.lift (I.subgroupOf (D.comap pi))
        (pi.subgroupComap D)
        (imageKernel_le_restrictedKernel pi D I hI))
      s₀.1 d generators hgen
  · haveI : IsEmpty (FixedImageKernelSubgroupFibre pi D I) :=
      not_nonempty_iff.mp hnonempty
    simp

variable (pi : G →* B) (hpi : Function.Surjective pi)

/-- The retained top axis is simply the image of the original normal
subgroup.  The apparently larger `ker pi ⊔ N` in its definition only makes
the descended quotient convenient definitionally. -/
theorem elementaryLayerTopAxis_val_eq_map
    (N : {N : Subgroup G // N.Normal}) :
    (elementaryLayerTopAxis pi hpi N).1 = N.1.map pi := by
  change (pi.ker ⊔ N.1).map pi = N.1.map pi
  rw [Subgroup.map_sup]
  have hker : pi.ker.map pi = ⊥ := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx
    · exact bot_le
  simp only [hker, bot_sup_eq]

end SymmetricSubgroupAsymptotics

end
