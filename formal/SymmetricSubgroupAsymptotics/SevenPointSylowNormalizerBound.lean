import SymmetricSubgroupAsymptotics.FiniteCyclicNormalizerCardBound
import SymmetricSubgroupAsymptotics.ElevenCycleOddInverter
import Mathlib.GroupTheory.Sylow

/-! The normalizer of an actual order-seven subgroup in a faithful
seven-point action has order at most42. The centralizer is bounded by
evaluation on the literal seven-cycle; no primitive action is classified. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SevenPointSylowNormalizerBound

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem cycle_centralizer_card (g : Equiv.Perm (Fin 7)) (hg : orderOf g = 7) :
    Nat.card (Subgroup.centralizer ({g} : Set (Equiv.Perm (Fin 7)))) = 7 := by
  have hc : g.IsCycle := Equiv.Perm.isCycle_of_prime_order'
    (by rw [hg]; decide) (by rw [hg]; decide)
  have hs : g.support.card = 7 := hc.orderOf.symm.trans hg
  rw [Equiv.Perm.nat_card_centralizer,hc.cycleType,hs]
  norm_num

variable {G : Type} [Group G] [Finite G] [MulAction G (Fin 7)]
    [FaithfulSMul G (Fin 7)]

theorem normalizer_card_le (P : Subgroup G) (hP : Nat.card P = 7) :
    Nat.card (Subgroup.normalizer (P : Set G)) ≤ 42 := by
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := P) 7 (by rw [hP])
  let f := MulAction.toPermHom G (Fin 7)
  have hf : Function.Injective f := MulAction.toPerm_injective
  have hgo : orderOf (f (g : G)) = 7 :=
    (orderOf_injective f hf (g : G)).trans
      ((Subgroup.orderOf_coe g).trans hg)
  let c : Subgroup.centralizer (P : Set G) →
      Subgroup.centralizer ({f (g : G)} : Set (Equiv.Perm (Fin 7))) := fun x =>
    ⟨f x.1,by
      apply Subgroup.mem_centralizer_iff.mpr
      intro y hy
      have hy' : y = f (g : G) := Set.mem_singleton_iff.mp hy
      subst y
      have hx := Subgroup.mem_centralizer_iff.mp x.2 (g : G) g.2
      change f (g : G) * f x.1 = f x.1 * f (g : G)
      simpa only [←map_mul] using congrArg f hx⟩
  have hc : Function.Injective c := by
    intro x y h
    apply Subtype.ext
    exact hf (congrArg Subtype.val h)
  have hcent : Nat.card (Subgroup.centralizer (P : Set G)) ≤ 7 :=
    (Nat.card_le_card_of_injective c hc).trans_eq (cycle_centralizer_card _ hgo)
  letI : IsCyclic P := isCyclic_of_prime_card hP
  have hAut : Nat.card (MulAut P) = 6 := by
    rw [IsCyclic.card_mulAut,hP]
    decide
  have hn := normalizer_card_le_centralizer_mul_aut P
  rw [hAut] at hn
  exact hn.trans (by omega)

end SymmetricSubgroupAsymptotics.SevenPointSylowNormalizerBound
