import SymmetricSubgroupAsymptotics.GeneratingPairPrimeProductOrder
import SymmetricSubgroupAsymptotics.External.CFSG.Models.Sporadic

/-! Eight actual pinned presentations have a prime product relator above
ten. The shared generating-pair argument makes its product nontrivial in
the noncommutative model, hence gives a genuine prime divisor of its order.
Only literal third/fourth relators are used, with no order table or action
catalogue. Other sporadic models are not asserted to satisfy this route. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSporadicPrimeProductDivisors

theorem m11_prime_dvd_order
    (hn : ¬ IsMulCommutative CFSG.Models.Presentations.M11.Model) :
    11 ∣ Nat.card CFSG.Models.Presentations.M11.Model := by
  apply GeneratingPairPrimeProductOrder.prime_dvd_presented_card
    CFSG.Models.Presentations.M11.relators 11 (by decide) ?_ hn
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))

theorem m12_prime_dvd_order
    (hn : ¬ IsMulCommutative CFSG.Models.Presentations.M12.Model) :
    11 ∣ Nat.card CFSG.Models.Presentations.M12.Model := by
  apply GeneratingPairPrimeProductOrder.prime_dvd_presented_card
    CFSG.Models.Presentations.M12.relators 11 (by decide) ?_ hn
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))

theorem m23_prime_dvd_order
    (hn : ¬ IsMulCommutative CFSG.Models.Presentations.M23.Model) :
    23 ∣ Nat.card CFSG.Models.Presentations.M23.Model := by
  apply GeneratingPairPrimeProductOrder.prime_dvd_presented_card
    CFSG.Models.Presentations.M23.relators 23 (by decide) ?_ hn
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))

theorem m24_prime_dvd_order
    (hn : ¬ IsMulCommutative CFSG.Models.Presentations.M24.Model) :
    23 ∣ Nat.card CFSG.Models.Presentations.M24.Model := by
  apply GeneratingPairPrimeProductOrder.prime_dvd_presented_card
    CFSG.Models.Presentations.M24.relators 23 (by decide) ?_ hn
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))

theorem j3_prime_dvd_order
    (hn : ¬ IsMulCommutative CFSG.Models.Presentations.J3.Model) :
    19 ∣ Nat.card CFSG.Models.Presentations.J3.Model := by
  apply GeneratingPairPrimeProductOrder.prime_dvd_presented_card
    CFSG.Models.Presentations.J3.relators 19 (by decide) ?_ hn
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))

theorem hs_prime_dvd_order
    (hn : ¬ IsMulCommutative CFSG.Models.Presentations.HS.Model) :
    11 ∣ Nat.card CFSG.Models.Presentations.HS.Model := by
  apply GeneratingPairPrimeProductOrder.prime_dvd_presented_card
    CFSG.Models.Presentations.HS.relators 11 (by decide) ?_ hn
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))

theorem mcl_prime_dvd_order
    (hn : ¬ IsMulCommutative CFSG.Models.Presentations.McL.Model) :
    11 ∣ Nat.card CFSG.Models.Presentations.McL.Model := by
  apply GeneratingPairPrimeProductOrder.prime_dvd_presented_card
    CFSG.Models.Presentations.McL.relators 11 (by decide) ?_ hn
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))

theorem he_prime_dvd_order
    (hn : ¬ IsMulCommutative CFSG.Models.Presentations.He.Model) :
    17 ∣ Nat.card CFSG.Models.Presentations.He.Model := by
  apply GeneratingPairPrimeProductOrder.prime_dvd_presented_card
    CFSG.Models.Presentations.He.relators 17 (by decide) ?_ hn
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))

end SymmetricSubgroupAsymptotics.CFSGSporadicPrimeProductDivisors
