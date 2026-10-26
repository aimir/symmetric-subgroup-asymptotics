import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoElevenNormalizerSolvable
import SymmetricSubgroupAsymptotics.CyclicSylowElevenNormalizerCard
import Mathlib.GroupTheory.Perm.Centralizer

/-! Exact normalizer and centralizer cardinalities for actual Sylow
eleven subgroups of the original22-point M22. Fixed-point-free order11
permutations have two11-cycles and ambient centralizer242. The generic
divisor/Sylow argument then gives normalizer55 and centralizer11. Neither
an order-eight class census nor an abstract automorphism bound is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoElevenNormalizerCard
open CFSGMathieuTwentyTwoActualOrder CFSGMathieuTwentyTwoElevenNormalizerSolvable

private instance modelFinite : Finite CFSG.Models.Mathieu22 := Finite.of_injective
  (fun g : CFSG.Models.Mathieu22 => g.val) Subtype.val_injective

private theorem ambient_centralizer_card (g : CFSG.Models.Mathieu22) (hg : orderOf g = 11) :
    Nat.card (Subgroup.centralizer ({g.val} : Set (Equiv.Perm (Fin 22)))) = 242 := by
  let σ : Equiv.Perm (Fin 22) := g.val
  have ho : orderOf σ = 11 := (Subgroup.orderOf_coe g).trans hg
  have hsupp : σ.support = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro i
    exact Equiv.Perm.mem_support.mpr (no_fixed_point_of_order_eleven g hg i)
  have hs : σ.cycleType.sum = 22 := by
    rw [Equiv.Perm.sum_cycleType,hsupp]
    simp
  obtain ⟨n,hn⟩ := Equiv.Perm.cycleType_prime_order (σ := σ) (by rw [ho]; decide)
  rw [hn] at hs
  simp only [Multiset.sum_replicate,nsmul_eq_mul,Nat.cast_id,ho] at hs
  have hn1 : n = 1 := by omega
  have hcycle : σ.cycleType = ({11,11} : Multiset ℕ) := by
    simpa only [hn1,ho] using hn
  change Nat.card (Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin 22)))) = 242
  rw [Equiv.Perm.nat_card_centralizer,hcycle]
  norm_num

theorem centralizer_card_dvd_twoFortyTwo (P : Sylow 11 CFSG.Models.Mathieu22) :
    Nat.card (Subgroup.centralizer (P : Set CFSG.Models.Mathieu22)) ∣ 242 := by
  letI : IsCyclic P := sylow_eleven_isCyclic P
  obtain ⟨z,hz⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic P)
  have hzo : orderOf z = 11 :=
    (orderOf_eq_card_of_zpowers_eq_top hz).trans (sylow_eleven_card P)
  have hg : orderOf (z.val : CFSG.Models.Mathieu22) = 11 :=
    (Subgroup.orderOf_coe z).trans hzo
  let C := Subgroup.centralizer (P : Set CFSG.Models.Mathieu22)
  let f : C →* Subgroup.centralizer
      ({z.val.val} : Set (Equiv.Perm (Fin 22))) := {
    toFun := fun x => ⟨x.val.val,by
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      have hx := Subgroup.mem_centralizer_iff.mp x.property z.val z.property
      exact (congrArg (fun u : CFSG.Models.Mathieu22 => u.val) hx).symm⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hf : Function.Injective f := by
    intro x y he
    have hval : x.val.val = y.val.val := congrArg
      (fun t : Subgroup.centralizer ({z.val.val} : Set (Equiv.Perm (Fin 22))) => t.val) he
    exact Subtype.ext (Subtype.ext hval)
  have hd := Subgroup.card_dvd_of_injective f hf
  rwa [ambient_centralizer_card z.val hg] at hd

theorem normalizer_card_eq_fiftyFive (P : Sylow 11 CFSG.Models.Mathieu22) :
    Nat.card (Subgroup.normalizer (P : Set CFSG.Models.Mathieu22)) = 55 :=
  CyclicSylowElevenNormalizerCard.normalizer_card_eq_fiftyFive P card (sylow_eleven_card P)
    (centralizer_card_dvd_twoFortyTwo P)

theorem centralizer_card_eq_eleven (P : Sylow 11 CFSG.Models.Mathieu22) :
    Nat.card (Subgroup.centralizer (P : Set CFSG.Models.Mathieu22)) = 11 :=
  CyclicSylowElevenNormalizerCard.centralizer_card_eq_eleven P card (sylow_eleven_card P)
    (centralizer_card_dvd_twoFortyTwo P)

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoElevenNormalizerCard
