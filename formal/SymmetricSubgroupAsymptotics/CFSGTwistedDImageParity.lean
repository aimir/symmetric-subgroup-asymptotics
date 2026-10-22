import SymmetricSubgroupAsymptotics.CFSGTwistedDNaturalA2Action
import SymmetricSubgroupAsymptotics.CFSGProjectiveLinearEvenOrder
import SymmetricSubgroupAsymptotics.CFSGSimpleProjectiveDescent

/-! The actual image of the derived fixed subgroup has a noncentral
fourth root of one in every characteristic. Simplicity is required only
for the SAME original twisted project's final central-quotient descent. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDFixedA2
open CFSGOrthogonalDSerreMatrices CFSGTwistedDA2MatrixWitness
variable (s : ℕ) (q : CFSG.PrimePower)

theorem image_weyl_four :
    ((derivedImageAction s q).rangeRestrict (weylWord s q)) ^ 4 = 1 := by
  apply Subtype.ext
  change (derivedImageAction s q (weylWord s q)) ^ 4 = 1
  rw [weylWord_image, ← map_pow, naturalWeyl_four, map_one]

theorem image_weyl_not_center :
    (derivedImageAction s q).rangeRestrict (weylWord s q) ∉
      Subgroup.center (derivedImageAction s q).range := by
  intro hc
  have hh := congrArg Subtype.val ((Subgroup.mem_center_iff.mp hc)
    ((derivedImageAction s q).rangeRestrict (positiveWord s q)))
  change derivedImageAction s q (positiveWord s q) * derivedImageAction s q (weylWord s q) =
    derivedImageAction s q (weylWord s q) * derivedImageAction s q (positiveWord s q) at hh
  rw [positiveWord_image, weylWord_image] at hh
  have hcomm : ⁅naturalAction s q
      (naturalWeyl (q.Extension 2) (s + 4) (coordinate s 0) (coordinate s 2)
        (coordinate_ne s (by decide))),
      naturalAction s q (chain (q.Extension 2) (s + 4) (coordinate s 0) (coordinate s 2)
        (coordinate_ne s (by decide)) 1)⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr hh.symm
  have hk : ⁅naturalWeyl (q.Extension 2) (s + 4) (coordinate s 0) (coordinate s 2)
        (coordinate_ne s (by decide)),
      chain (q.Extension 2) (s + 4) (coordinate s 0) (coordinate s 2)
        (coordinate_ne s (by decide)) 1⁆ ∈ (naturalAction s q).ker := by
    change naturalAction s q _ = 1
    rw [map_commutatorElement]
    exact hcomm
  change _ ∈ (elementaryImageAction (q.Extension 2) (s + 4) (by omega)).ker at hk
  rw [elementaryImageAction_ker (q.Extension 2) s] at hk
  exact naturalWeyl_commutator_not_center (q.Extension 2) s
    (coordinate s 0) (coordinate s 2) (coordinate_ne s (by decide)) hk

theorem image_projective_even_card :
    Even (Nat.card ((derivedImageAction s q).range ⧸
      Subgroup.center (derivedImageAction s q).range)) := by
  let Q := QuotientGroup.mk' (Subgroup.center (derivedImageAction s q).range)
  apply CFSGProjectiveLinearEvenOrder.even_card_of_nontrivial_fourth_root
    (Q ((derivedImageAction s q).rangeRestrict (weylWord s q)))
  · intro h
    exact image_weyl_not_center s q ((QuotientGroup.eq_one_iff _).mp h)
  · exact (map_pow Q ((derivedImageAction s q).rangeRestrict (weylWord s q)) 4).symm.trans
      ((congrArg Q (image_weyl_four s q)).trans (map_one Q))

theorem twistedD_even_card_shift
    [IsSimpleGroup (CFSG.Models.TwistedD (s + 4) q)] :
    Even (Nat.card (CFSG.Models.TwistedD (s + 4) q)) := by
  let f := derivedImageAction s q
  let Q := QuotientGroup.mk' (Subgroup.center f.range)
  have hne : Q (f.rangeRestrict (weylWord s q)) ≠ 1 := by
    intro h
    exact image_weyl_not_center s q ((QuotientGroup.eq_one_iff _).mp h)
  letI : Nontrivial (f.range ⧸ Subgroup.center f.range) :=
    ⟨⟨Q (f.rangeRestrict (weylWord s q)), 1, hne⟩⟩
  let e := CFSGSimpleProjectiveDescent.projectiveEquivOfSimple
    f.rangeRestrict f.rangeRestrict_surjective
  change Even (Nat.card (Derived s q ⧸ Subgroup.center (Derived s q)))
  rw [Nat.card_congr e.toEquiv]
  exact image_projective_even_card s q

theorem twistedD_even_card (r : ℕ) (hr : 4 ≤ r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedD r q)] :
    Even (Nat.card (CFSG.Models.TwistedD r q)) := by
  obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le hr
  have he : r = s + 4 := by omega
  clear hs
  subst r
  exact twistedD_even_card_shift s q

end SymmetricSubgroupAsymptotics.CFSGTwistedDFixedA2
