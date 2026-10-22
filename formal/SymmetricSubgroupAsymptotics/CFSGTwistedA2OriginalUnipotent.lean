import SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentGroup
import SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentFixed
import SymmetricSubgroupAsymptotics.CFSGTwistedAFixedLiftPullback

/-! An actual q^3 p-subgroup in the ORIGINAL rank-two fixed source.
Its injection is proved using the actual natural-action kernel and the
literal unitriangular diagonal. No full-SU realization or Sylow claim is
made here; the original derived-group inclusion is a separate step. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
open CFSG.Models.Chevalley CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists
open CFSGTwistedA2OriginalRelations

theorem naturalUnipotent_fixed (q : CFSG.PrimePower) (g : naturalUnipotent q) :
    diagramFieldUnitHom (q.Extension 2) 2 (definingFieldAutomorphism q 2).toRingHom
      g.val.val = g.val.val := by
  obtain ⟨a, b, hab, hg⟩ := g.property
  rw [hg]
  exact upperNatural_fixed _ _ (fun x => extension_two_pow_twice q x) a b hab

def unipotentToOriginalFixed (q : CFSG.PrimePower) : naturalUnipotent q →* OriginalFixedA 2 q where
  toFun g := fixedElementOfNaturalUnit q g.val (naturalUnipotent_fixed q g)
  map_one' := by
    apply Subtype.ext
    exact congrArg (fun g : Model A (q.Extension 2) => g.val)
      (map_one (elementaryToModel (q.Extension 2)))
  map_mul' g h := by
    apply Subtype.ext
    exact congrArg (fun g : Model A (q.Extension 2) => g.val)
      (map_mul (elementaryToModel (q.Extension 2)) g.val h.val)

theorem unipotentToOriginalFixed_injective (q : CFSG.PrimePower) :
    Function.Injective (unipotentToOriginalFixed q) := by
  apply (unipotentToOriginalFixed q).ker_eq_bot_iff.mp
  apply bot_unique
  intro g hg
  change g = 1
  change unipotentToOriginalFixed q g = 1 at hg
  have hsource : elementaryToModel (q.Extension 2) g.val = 1 := by
    apply Subtype.ext
    exact congrArg (fun h : OriginalFixedA 2 q => h.val) hg
  have haction : naturalElementaryAction (q.Extension 2) 2 g.val = 1 := by
    rw [← elementaryToModel_action, hsource, map_one]
  have hk : g.val ∈ (naturalElementaryAction (q.Extension 2) 2).ker := haction
  rw [naturalElementaryAction_ker (q.Extension 2) 2 (by decide)] at hk
  obtain ⟨c, hc⟩ := (naturalElementary_center_iff_scalar (q.Extension 2) 2 (by decide) g.val).mp hk
  obtain ⟨a, b, hab, hgparam⟩ := g.property
  have hdiag : (g.val.val : Mat (q.Extension 2) 2) 0 0 = 1 := by
    rw [hgparam, upperNatural_val]
    simp [upperArray]
  have hs := congrArg (fun M : Mat (q.Extension 2) 2 => M 0 0) hc
  change (g.val.val : Mat (q.Extension 2) 2) 0 0 = (c • (1 : Mat (q.Extension 2) 2)) 0 0 at hs
  rw [hdiag] at hs
  have hcone : c = 1 := by simpa only [Matrix.smul_apply, Matrix.one_apply,
    if_true, smul_eq_mul, mul_one] using hs.symm
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  change (g.val.val : Mat (q.Extension 2) 2) = 1
  rw [hc, hcone, one_smul]

def originalUnipotent (q : CFSG.PrimePower) : Subgroup (OriginalFixedA 2 q) :=
  (unipotentToOriginalFixed q).range

theorem originalUnipotent_card (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    Nat.card (originalUnipotent q) = q.order ^ 3 :=
  (Nat.card_congr (MonoidHom.ofInjective (unipotentToOriginalFixed_injective q)).symm.toEquiv).trans
    (naturalUnipotent_card q hq)

theorem originalUnipotent_isPGroup (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    IsPGroup q.prime (originalUnipotent q) := by
  apply IsPGroup.of_card (n := q.exponent * 3)
  rw [originalUnipotent_card q hq]
  exact (pow_mul q.prime q.exponent 3).symm

end SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
