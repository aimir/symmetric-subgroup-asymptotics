import SymmetricSubgroupAsymptotics.CFSGSymplecticPointAffineKernel
import SymmetricSubgroupAsymptotics.CFSGSymplecticPointAffineSurjective
import SymmetricSubgroupAsymptotics.ConjugacyClassExtension
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! The literal point stabilizer has at most q times the class number
of its actual affine tail quotient. This uses its actual kernel, whose
cardinality is at most q, and the proved surjective homomorphism. The
rank-one base follows from the same kernel argument at tail rank zero. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGSymplecticPointClassExtension
open CFSGSymplecticSerreMatrices CFSGSymplecticPointAffineHom
open CFSGSymplecticPointAffineKernel CFSGSymplecticPointAffineSurjective
open LinearSemidirectCommutingFibres
variable (K : Type) [Field K]

local instance finitePoint [Finite K] (r : ℕ) : Finite (pointStabilizer K r) :=
  Finite.of_injective (fun g : pointStabilizer K r => (g.val.val : Mat K (r+1)))
    (by
      intro g h he
      apply Subtype.ext
      apply Subtype.ext
      apply Units.ext
      exact he)

theorem class_card_le_affine [Finite K] (r : ℕ) (hr : 0 < r) :
    Nat.card (ConjClasses (pointStabilizer K r)) ≤
      Nat.card K * Nat.card (ConjClasses (AffineGroup (naturalLinearHom K r))) := by
  let f := pointAffineHom K r
  have hs : Function.Surjective f := pointAffineHom_surjective K r hr
  letI : Finite (AffineGroup (naturalLinearHom K r)) := Finite.of_surjective f hs
  have hk : Nat.card (ConjClasses f.ker) ≤ Nat.card K :=
    (Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective).trans
      (kernel_card_le K r)
  let e := QuotientGroup.quotientKerEquivOfSurjective f hs
  have hq : Nat.card (ConjClasses ((pointStabilizer K r) ⧸ f.ker)) ≤
      Nat.card (ConjClasses (AffineGroup (naturalLinearHom K r))) :=
    Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
      (ConjClasses.map_surjective e.symm.surjective)
  exact (conjugacyClass_card_le_normal_mul_quotient f.ker).trans
    (Nat.mul_le_mul hk hq)

theorem rankOne_class_card_le [Finite K] :
    Nat.card (ConjClasses (pointStabilizer K 0)) ≤ Nat.card K := by
  letI : Subsingleton (AffineGroup (naturalLinearHom K 0)) := ⟨fun a b =>
    SemidirectProduct.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩
  let k : pointStabilizer K 0 → (pointAffineHom K 0).ker :=
    fun g => ⟨g,Subsingleton.elim _ _⟩
  let c : pointStabilizer K 0 → K := fun g => kernelCoordinate K 0 (k g)
  have hc : Function.Injective c := by
    intro g h he
    have hk : k g = k h := kernelCoordinate_injective K 0 he
    exact congrArg (fun a : (pointAffineHom K 0).ker => a.val) hk
  exact (Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective).trans
    (Nat.card_le_card_of_injective c hc)

end SymmetricSubgroupAsymptotics.CFSGSymplecticPointClassExtension
