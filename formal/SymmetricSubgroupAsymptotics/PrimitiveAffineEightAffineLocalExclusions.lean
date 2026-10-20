import SymmetricSubgroupAsymptotics.AffineZeroStabilizer
import SymmetricSubgroupAsymptotics.SmallTernaryQuotientObstructions
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow20AffineSocleClosure

/-!
The actual literal affine groups of orders 56 and 1344 have no eligible
binary-plane quotient on their point stabilizers. The previously checked
affine charts identify the stabilizers with the actual generated linear
complements of orders 7 and 168; both complements are simple. No new
enumeration of either group or its normal subgroups is used.

Matching these literal actions with a published catalogue ID is a separate
correspondence obligation. The assertions below concern the displayed
original permutation groups and their actual stabilizers.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoPairedEightAffineTops

theorem pointEquiv_zero : pointEquiv (0 : Vector) = (0 : Fin 8) := by
  decide +kernel

namespace Row18

theorem modelEquiv_action (g : Top) (v : Vector) :
    pointEquiv (AffineModel.action linearGroup (modelEquiv g) v) =
      g.1 (pointEquiv v) := by
  have he : affineAction linearGroup (modelEquiv g) = g.1 :=
    congrArg (fun x : Top => x.1) (modelEquiv.symm_apply_apply g)
  have hv := DFunLike.congr_fun he (pointEquiv v)
  change pointEquiv (AffineModel.action linearGroup (modelEquiv g)
    (pointEquiv.symm (pointEquiv v))) = g.1 (pointEquiv v) at hv
  simpa only [Equiv.symm_apply_apply] using hv

/-- The original literal point stabilizer is the generated order-seven
linear group, through the action-preserving affine coordinates. -/
def pointStabilizerEquiv : MulAction.stabilizer Top (0 : Fin 8) ≃* linearGroup := by
  simpa only [pointEquiv_zero] using
    AffineModel.pointStabilizerEquiv linearGroup Top modelEquiv pointEquiv modelEquiv_action

theorem no_eligible_pointStabilizer_quotient
    {Q : Type} [Group Q] [Finite Q]
    (f : MulAction.stabilizer Top (0 : Fin 8) →* Q)
    (hQ : Nat.card Q = 3 ∨ Nat.card Q = 6) :
    ¬ Function.Surjective f := by
  letI : IsSimpleGroup linearGroup := linearGroup_isSimpleGroup
  intro hf
  exact not_surjective_three_or_six_of_simple
    (by rw [linearGroup_card]; decide)
    (f.comp pointStabilizerEquiv.symm.toMonoidHom) hQ
    (hf.comp pointStabilizerEquiv.symm.surjective)

end Row18

namespace Row20

theorem modelEquiv_action (g : Top) (v : Vector) :
    pointEquiv (AffineModel.action linearGroup (modelEquiv g) v) =
      g.1 (pointEquiv v) := by
  have he : affineAction linearGroup (modelEquiv g) = g.1 :=
    congrArg (fun x : Top => x.1) (modelEquiv.symm_apply_apply g)
  have hv := DFunLike.congr_fun he (pointEquiv v)
  change pointEquiv (AffineModel.action linearGroup (modelEquiv g)
    (pointEquiv.symm (pointEquiv v))) = g.1 (pointEquiv v) at hv
  simpa only [Equiv.symm_apply_apply] using hv

/-- The order is transported from the already checked selected linear
certificate, retaining the same two generators as the affine chart. -/
theorem linearComplement_card : Nat.card linearGroup = 168 := by
  letI : Group PrimitiveAffineDegreeTwoPairedEightRow20LinearTopCertificate.Source :=
    PrimitiveAffineDegreeTwoPairedEightRow20LinearTopCertificate.group
  let e := linearTopEquiv.trans
    (MulEquiv.subgroupCongr linearTop_eq_selectedClosure)
  calc
    Nat.card linearGroup = Nat.card
        (Subgroup.closure (Set.range
          PrimitiveAffineDegreeTwoPairedEightRow20LinearTopCertificate.generators)) :=
      Nat.card_congr e.toEquiv
    _ = Nat.card PrimitiveAffineDegreeTwoPairedEightRow20LinearTopCertificate.Source :=
      Nat.card_congr
        PrimitiveAffineDegreeTwoPairedEightRow20LinearTopCertificate.originalEquiv.symm.toEquiv
    _ = 168 := PrimitiveAffineDegreeTwoPairedEightRow20LinearTopCertificate.source_card

def pointStabilizerEquiv : MulAction.stabilizer Top (0 : Fin 8) ≃* linearGroup := by
  simpa only [pointEquiv_zero] using
    AffineModel.pointStabilizerEquiv linearGroup Top modelEquiv pointEquiv modelEquiv_action

theorem no_eligible_pointStabilizer_quotient
    {Q : Type} [Group Q] [Finite Q]
    (f : MulAction.stabilizer Top (0 : Fin 8) →* Q)
    (hQ : Nat.card Q = 3 ∨ Nat.card Q = 6) :
    ¬ Function.Surjective f := by
  letI : IsSimpleGroup linearGroup := linearGroup_isSimpleGroup
  intro hf
  exact not_surjective_three_or_six_of_simple
    (by rw [linearComplement_card]; decide)
    (f.comp pointStabilizerEquiv.symm.toMonoidHom) hQ
    (hf.comp pointStabilizerEquiv.symm.surjective)

end Row20
end PrimitiveAffineDegreeTwoPairedEightAffineTops
end SymmetricSubgroupAsymptotics

end
