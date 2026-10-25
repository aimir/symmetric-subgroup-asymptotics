import SymmetricSubgroupAsymptotics.FiveCycleInvolutionOrbitCommutation
import SymmetricSubgroupAsymptotics.External.CFSG.Models.Presentations.Co2

/-! The pinned Co2 presentation becomes solvable if its actual group
has no element of order four. Its two fourth-power commutator relators
then become square-one relations, forcing the involution's cyclic
five-orbit to commute. This is literal presentation algebra, not an order
or action catalogue. The source need not already be known simple. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGCoTwoElementarySylowSolvability
open CFSG.Models CyclicConjugateOrbitSolvable

private def generators : Fin 2 → Presentations.Co2.Model := PresentedGroup.of

theorem x_square : (generators 0)^2 = 1 := by
  have h := PresentedGroup.one_of_mem
    (rels := {w | w ∈ Presentations.Co2.relators}) (x := (FreeGroup.of (0 : Fin 2))^2)
    (by change _ ∈ Presentations.Co2.relators
        exact List.mem_cons_self)
  simpa only [generators,commWord,map_pow,map_mul,map_inv,PresentedGroup.of] using h

theorem y_fifth : (generators 1)^5 = 1 := by
  have h := PresentedGroup.one_of_mem
    (rels := {w | w ∈ Presentations.Co2.relators}) (x := (FreeGroup.of (1 : Fin 2))^5)
    (by change _ ∈ Presentations.Co2.relators
        exact List.mem_cons_of_mem _ (List.mem_cons_self))
  simpa only [generators,commWord,map_pow,map_mul,map_inv,PresentedGroup.of] using h

theorem first_commutator_fourth : (commWord (generators 0) (generators 1))^4 = 1 := by
  have h := PresentedGroup.one_of_mem
    (rels := {w | w ∈ Presentations.Co2.relators}) (x := (commWord (FreeGroup.of (0 : Fin 2)) (FreeGroup.of (1 : Fin 2)))^4)
    (by change _ ∈ Presentations.Co2.relators
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
  simpa only [generators,commWord,map_pow,map_mul,map_inv,PresentedGroup.of] using h

theorem second_commutator_fourth : (commWord (generators 0) ((generators 1)^2))^4 = 1 := by
  have h := PresentedGroup.one_of_mem
    (rels := {w | w ∈ Presentations.Co2.relators}) (x := (commWord (FreeGroup.of (0 : Fin 2)) ((FreeGroup.of (1 : Fin 2))^2))^4)
    (by change _ ∈ Presentations.Co2.relators
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
  simpa only [generators,commWord,map_pow,map_mul,map_inv,PresentedGroup.of] using h

theorem isSolvable_of_no_order_four
    (hno : ¬∃ g : Presentations.Co2.Model, orderOf g = 4) : IsSolvable Presentations.Co2.Model := by
  have hsecondPower (z : Presentations.Co2.Model) (hz : z^4 = 1) : z^2 = 1 := by
    by_contra h
    exact hno ⟨z,orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using h) (by simpa using hz)⟩
  have hc1 := hsecondPower _ first_commutator_fourth
  have hc2 := hsecondPower _ second_commutator_fourth
  have hxi : (generators 0)⁻¹ = generators 0 :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using x_square)
  have hfirst : (generators 0*orbit (generators 0) (generators 1) (-1))^2 = 1 := by
    simpa only [commWord,hxi,orbit,MulAut.conj_apply,zpow_neg_one,inv_inv,mul_assoc] using hc1
  have hsecond : (generators 0*orbit (generators 0) (generators 1) (-2))^2 = 1 := by
    simpa only [commWord,hxi,orbit,MulAut.conj_apply,zpow_neg,zpow_ofNat,inv_inv,mul_assoc] using hc2
  exact FiveCycleInvolutionOrbitCommutation.isSolvable_of_five_and_two_offsets generators
    (PresentedGroup.closure_range_of _) x_square y_fifth hfirst hsecond

end SymmetricSubgroupAsymptotics.CFSGCoTwoElementarySylowSolvability
