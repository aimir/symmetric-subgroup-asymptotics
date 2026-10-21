import SymmetricSubgroupAsymptotics.CFSGAlternatingOrderThreeCentralizers
import SymmetricSubgroupAsymptotics.CFSGAlternatingThreeCycleNumerics
import SymmetricSubgroupAsymptotics.FiniteConjugacyCentralizerCoordinateTransport
import Mathlib.Tactic.NormNum

/-! Every automorphism of A_n preserves actual single three-cycles when
n≥5 and n≠6. The proof uses element order, exact actual centralizer order
and a uniform factorial inequality. Degree6 is explicitly kept separate:
its order-three images can have either one or two three-cycles. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGAlternatingThreeCyclePreservation
open CFSGAlternatingOrderThreeCentralizers

private theorem image_order_three (n : ℕ) (f : MulAut (alternatingGroup (Fin n)))
    (g : alternatingGroup (Fin n)) (hg : g.val.IsThreeCycle) : orderOf (f g).val=3 :=
  (Subgroup.orderOf_coe (f g)).trans ((f.orderOf_eq g).trans
    ((Subgroup.orderOf_coe g).symm.trans hg.orderOf))

/-- The class of actual single three-cycles is characteristic outside
exactly the exceptional degree allowed by the centralizer equation. -/
theorem map_isThreeCycle (n : ℕ) (hn : 5≤n) (hne : n≠6)
    (f : MulAut (alternatingGroup (Fin n)))
    (g : alternatingGroup (Fin n)) (hg : g.val.IsThreeCycle) : (f g).val.IsThreeCycle := by
  obtain ⟨k,hk,hkn,htype,hfactor⟩ := order_three_profile n hn (f g) (image_order_three n f g hg)
  have hcent : Nat.card (Subgroup.centralizer ({f g} : Set (alternatingGroup (Fin n))))=
      Nat.card (Subgroup.centralizer ({g} : Set (alternatingGroup (Fin n)))) :=
    (Nat.card_congr (centralizerSingletonMulEquiv f g).toEquiv).symm
  have hsingle := alternating_centralizer_factor n hn g 1 (by decide)
    (show g.val.cycleType=Multiset.replicate 1 3 from by simpa only [Multiset.replicate_one] using hg.cycleType)
  norm_num only [pow_one,Nat.factorial_one,Nat.mul_one] at hsingle
  rw [hcent] at hfactor
  have he : 3^k*k.factorial*(n-3*k).factorial=3*(n-3).factorial := hfactor.symm.trans hsingle
  have hk1 := CFSGAlternatingThreeCycleNumerics.equality_forces_single n k hn hk hkn hne he
  change (f g).val.cycleType={3}
  simpa only [hk1,Multiset.replicate_one] using htype

theorem map_isThreeCycle_iff (n : ℕ) (hn : 5≤n) (hne : n≠6)
    (f : MulAut (alternatingGroup (Fin n))) (g : alternatingGroup (Fin n)) :
    (f g).val.IsThreeCycle ↔ g.val.IsThreeCycle := by
  constructor
  · intro hg
    simpa only [f.symm_apply_apply] using map_isThreeCycle n hn hne f.symm (f g) hg
  · exact map_isThreeCycle n hn hne f g

/-- No false single-class preservation is asserted at degree6. -/
theorem map_three_cycle_six_type (f : MulAut (alternatingGroup (Fin 6)))
    (g : alternatingGroup (Fin 6)) (hg : g.val.IsThreeCycle) :
    (f g).val.cycleType={3} ∨ (f g).val.cycleType={3,3} := by
  obtain ⟨k,hk,hkn,htype,_⟩ := order_three_profile 6 (by decide) (f g) (image_order_three 6 f g hg)
  have hcases : k=1 ∨ k=2 := by omega
  rcases hcases with rfl|rfl
  · exact Or.inl (by simpa only [Multiset.replicate_one] using htype)
  · exact Or.inr (by simpa only [Multiset.replicate_succ,Multiset.replicate_zero] using htype)

end SymmetricSubgroupAsymptotics.CFSGAlternatingThreeCyclePreservation
