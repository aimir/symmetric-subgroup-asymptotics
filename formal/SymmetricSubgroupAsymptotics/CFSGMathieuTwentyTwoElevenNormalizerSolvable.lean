import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoActualOrder
import SymmetricSubgroupAsymptotics.TwoCyclePermutationCentralizerSolvable
import SymmetricSubgroupAsymptotics.CyclicNormalizerSolvableOfCentralizer

/-! The SAME actual pinned M22 has cyclic Sylow11 subgroups with soluble
normalizers. Order11 elements act without fixed points on22 points, so
their ambient centralizers have at most two cycle factors. The separate
two-Sylow generation obligation is neither assumed nor concluded. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoElevenNormalizerSolvable
open CFSGMathieuTwentyTwoActualOrder

theorem centralizer_isSolvable (g : CFSG.Models.Mathieu22) (hg : orderOf g=11) :
    IsSolvable (Subgroup.centralizer ({g} : Set CFSG.Models.Mathieu22)) := by
  let σ : Equiv.Perm (Fin 22) := g.val
  have ho : orderOf σ=11 := (Subgroup.orderOf_coe g).trans hg
  obtain ⟨n,hn⟩ := Equiv.Perm.cycleType_prime_order (σ:=σ) (by rw [ho]; decide)
  have hs := σ.sum_cycleType_le
  rw [hn] at hs
  simp only [Multiset.sum_replicate,ho,smul_eq_mul,Fintype.card_fin] at hs
  have hc : Nat.card σ.cycleFactorsFinset≤2 := by
    have he : Nat.card σ.cycleFactorsFinset=σ.cycleType.card := by
      simp only [Nat.card_eq_fintype_card,Fintype.card_coe,Equiv.Perm.cycleType_def,
        Multiset.card_map,Finset.card_val]
    rw [he,hn,Multiset.card_replicate]
    omega
  letI : IsSolvable (Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin 22)))) :=
    TwoCyclePermutationCentralizerSolvable.isSolvable σ
      (no_fixed_point_of_order_eleven g hg) hc
  let C := Subgroup.centralizer ({g} : Set CFSG.Models.Mathieu22)
  let f : C →* Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin 22))) := {
    toFun := fun x => ⟨x.val.val,by
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      have hcomm := Subgroup.mem_centralizer_singleton_iff.mp x.property
      exact congrArg (fun z : CFSG.Models.Mathieu22 => z.val) hcomm⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  apply solvable_of_solvable_injective (f:=f)
  intro x y h
  have he : x.val.val=y.val.val := congrArg
    (fun z : Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin 22))) => z.val) h
  exact Subtype.ext (Subtype.ext he)

theorem sylow_eleven_isCyclic (P : Sylow 11 CFSG.Models.Mathieu22) : IsCyclic P := by
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  exact isCyclic_of_prime_card (sylow_eleven_card P)

theorem normalizer_isSolvable (P : Sylow 11 CFSG.Models.Mathieu22) :
    IsSolvable (Subgroup.normalizer (P : Set CFSG.Models.Mathieu22)) := by
  letI : IsCyclic P := sylow_eleven_isCyclic P
  obtain ⟨x,hx⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic P)
  have hxorder : orderOf x=11 :=
    (orderOf_eq_card_of_zpowers_eq_top hx).trans (sylow_eleven_card P)
  have hg : orderOf (x.val : CFSG.Models.Mathieu22)=11 :=
    (Subgroup.orderOf_coe x).trans hxorder
  letI : IsSolvable (Subgroup.centralizer ({x.val} : Set CFSG.Models.Mathieu22)) :=
    centralizer_isSolvable x.val hg
  have hle : Subgroup.centralizer (P : Set CFSG.Models.Mathieu22)≤
      Subgroup.centralizer ({x.val} : Set CFSG.Models.Mathieu22) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr x.property)
  have hC : IsSolvable (Subgroup.centralizer (P : Set CFSG.Models.Mathieu22)) :=
    solvable_of_solvable_injective (f:=Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  exact CyclicNormalizerSolvableOfCentralizer.isSolvable (P : Subgroup CFSG.Models.Mathieu22) hC

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoElevenNormalizerSolvable
