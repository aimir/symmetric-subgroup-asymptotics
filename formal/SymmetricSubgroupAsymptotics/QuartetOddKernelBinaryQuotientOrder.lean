import SymmetricSubgroupAsymptotics.OriginalKernelOddFixedFreeBinaryQuotient
import SymmetricSubgroupAsymptotics.BinaryPlaneWreathActualOddKernelConsequences
import SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingKernelPartition
import SymmetricSubgroupAsymptotics.BinaryPlaneLinearSymmetricEquiv
import SymmetricSubgroupAsymptotics.PermutationalWreathFinite

/-! Every binary quotient of an actual four-quartet affine action with
nonzero odd local kernel has order at most 128. The fixed-free original
translation kernel is killed first; the same quotient factors through the
actual linear image, whose full ambient binary part has order 128. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.QuartetOddKernelBinaryQuotientOrder
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open BinaryPlaneAlternatingKernelPartition (Frame)
open BinaryPlaneWreathActualOddKernel

 theorem frame_card : Nat.card Frame=2^7*3^5 := by
  rw [PermutationalWreathProduct.natCard_eq,
    BinaryPlaneLinearSymmetricEquiv.linear_card_six,Nat.card_fin,Nat.card_perm,Nat.card_fin]
  norm_num

 theorem quotient_card_le {G : Type} [Group G] [Finite G]
    (C : Subgroup Frame) (hO : oddKernel C≠⊥)
    (htrans : ∀ i k : Fin 4,∃ h : C,(h : Frame).right • i=k)
    (pi : G →* C) (hpi : Function.Surjective pi)
    (A : Rep.{0} (ZMod 2) C) (E : OriginalKernelModuleChart pi A)
    (j : Representation.IntertwiningMap A.ρ (BinaryPlaneCyclicWreathUniform.representation C))
    (hj : Function.Injective j)
    (N : Subgroup G) [N.Normal] (hQ : IsPGroup 2 (G ⧸ N)) :
    Nat.card (G ⧸ N)≤2^7 := by
  let O := oddKernel C
  letI : NeZero (Nat.card O : ZMod 2) := ⟨card_cast_ne_zero C⟩
  have hlocal : ∀ i : Fin 4,∃ o : O,localLinear C i o≠1 :=
    all_local_nontrivial C hO htrans
  have hfixed : ∀ a : A,(∀ o : O,A.ρ (o : C) a=a) → a=0 := by
    intro a ha
    apply hj
    have hz := fixedFree C hlocal (j a) (fun o => by
      rw [←Representation.IntertwiningMap.isIntertwining _ _ j (o : C) a,ha o])
    simpa only [map_zero] using hz
  obtain ⟨f,hf,_⟩ := E.binary_quotient_factors_top pi hpi A O
    (cube_eq_one C) hfixed N hQ
  have hd : Nat.card (G ⧸ N)∣2^7*3^5 := by
    rw [←frame_card]
    exact (Subgroup.card_dvd_of_surjective f hf).trans C.card_subgroup_dvd_card
  obtain ⟨n,hn⟩ := hQ.exists_card_eq
  have hc : Nat.Coprime (Nat.card (G ⧸ N)) (3^5) := by
    rw [hn]
    exact ((by decide : Nat.Coprime 2 3).pow_left n).pow_right 5
  exact Nat.le_of_dvd (by decide) (hc.dvd_of_dvd_mul_right hd)

end SymmetricSubgroupAsymptotics.QuartetOddKernelBinaryQuotientOrder
