import SymmetricSubgroupAsymptotics.CFSGFFourE6PositiveCartanKernel
import SymmetricSubgroupAsymptotics.CFSGFFourE6PositiveSylow
import SymmetricSubgroupAsymptotics.CFSGFFourOriginalGoodSylow
import Mathlib.SetTheory.Cardinal.Finite

/-! The actual positive Sylow injects into the SAME original F4 action
image, so its cardinality survives that surjective source-image step.
This is not yet a claim about the further quotient by the image centre. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6PositiveActionInjective
open CFSGFFourSerreMatrices CFSGFFourOriginalGoodSylow CFSGFFourE6PositiveSylow
open CFSGFFourE6PositiveCartanKernel CFSGFFourE6RegularPositive
open CFSGSerreQuadraticMatrix

local instance imageFinite (K : Type) [Field K] [Finite K] : Finite (imageGroup K) :=
  Finite.of_surjective (foldedToImage K) (foldedToImage_surjective K)

def positiveRestriction (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] : positiveSylow K p →* imageGroup K :=
  (foldedToImage K).comp (positiveSylow K p :
    Subgroup (canonicalElementaryGroup realizationData K)).subtype

theorem positiveRestriction_injective (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] : Function.Injective (positiveRestriction K p) := by
  apply (positiveRestriction K p).ker_eq_bot_iff.mp
  apply le_antisymm _ bot_le
  intro x hx
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  apply image_kernel_eq_one_of_positive K x.val
  · have he : positiveRestriction K p x=1 := hx
    have hv := congrArg (fun z : imageGroup K=>z.val) he
    change fullNaturalImageAction K x.val=1 at hv
    exact hv
  · have hP : (positiveSylow K p : Subgroup (canonicalElementaryGroup realizationData K)) ≤
        (E6Positive K).subgroupOf (canonicalElementaryGroup realizationData K) :=
      le_of_eq (positiveSylow_coe K p)
    exact hP x.property

def imagePositiveSylow (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] : Sylow p (imageGroup K) :=
  (positiveSylow K p).mapSurjective (f:=foldedToImage K) (foldedToImage_surjective K)

theorem imagePositiveSylow_card (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    Nat.card (imagePositiveSylow K p)=Nat.card (positiveSylow K p) := by
  have hc := Nat.card_congr
    (MonoidHom.ofInjective (positiveRestriction_injective K p)).symm.toEquiv
  have he : (positiveRestriction K p).range =
      (positiveSylow K p : Subgroup (canonicalElementaryGroup realizationData K)).map
        (foldedToImage K) := by
    rw [positiveRestriction,MonoidHom.range_comp,Subgroup.range_subtype]
  rw [he] at hc
  exact hc

end SymmetricSubgroupAsymptotics.CFSGFFourE6PositiveActionInjective
