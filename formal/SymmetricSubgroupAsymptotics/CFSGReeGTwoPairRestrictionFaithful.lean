import SymmetricSubgroupAsymptotics.CFSGReeGTwoRootRestrictionFaithful
import SymmetricSubgroupAsymptotics.CFSGReeGTwoPairRestriction

/-! The actual derived opposite-pair stabilizer restricts faithfully to
its same positive Ree subgroup. Transitivity on the other Sylows, not an
assumed rank-one recognition theorem, discharges the kernel. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoPairRestrictionFaithful
open CFSGReeGTwoPairRestriction CFSGReeGTwoRootRestrictionFaithful

theorem pairRestriction_injective (m : ℕ) (hm : 1≤m)
    [IsSimpleGroup (CFSG.Models.ReeG2 m)] : Function.Injective (pairRestriction m hm) := by
  apply (MonoidHom.ker_eq_bot_iff (pairRestriction m hm)).mp
  apply bot_unique
  intro f hf
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  apply eq_one_of_fixed_positive_and_opposite m hm f.val
    (pair_preserves_positive m hm f) (pair_preserves_opposite m hm f)
  intro u
  have he := congrArg (fun A : MulAut (CFSGReeGTwoOriginalPositiveSubgroup.fixedPositiveGroup m) =>
    (A (derivedPositiveEquiv m hm u)).val) hf
  apply Subtype.ext
  exact he

end SymmetricSubgroupAsymptotics.CFSGReeGTwoPairRestrictionFaithful
