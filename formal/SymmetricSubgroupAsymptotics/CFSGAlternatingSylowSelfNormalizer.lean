import SymmetricSubgroupAsymptotics.CFSGAlternatingNormalizerSmallClasses
import SymmetricSubgroupAsymptotics.CFSGNormalizerMatchingCentralizer
import SymmetricSubgroupAsymptotics.CFSGAlternatingSylowAmbientNormalizer
import SymmetricSubgroupAsymptotics.CFSGInvolutionCycleActionOddKernel
import SymmetricSubgroupAsymptotics.CFSGSignKernelImage
import SymmetricSubgroupAsymptotics.CFSGSymmetricImageNormalizer

/-! Every alternating Sylow two-subgroup in degree at least six is
self-normalizing. Its full symmetric normalizer preserves the intrinsic
matching of a containing symmetric Sylow. The even part has the full
cycle image because the cycle kernel contains an actual odd element. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGAlternatingSylowSelfNormalizer
open Equiv Perm CFSGSymmetricSylowCanonicalMatching
open CFSGInvolutionCentralizerTwoKernel

 theorem ambient_normalizer_isPGroup {X : Type*} [Fintype X] [DecidableEq X]
    (P : Sylow 2 (alternatingGroup X)) (hn : 6 ≤ Nat.card X) :
    IsPGroup 2 (Subgroup.normalizer
      (((P : Subgroup (alternatingGroup X)).map (alternatingGroup X).subtype) : Set (Perm X))) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let A := alternatingGroup X
  let H0 := (P : Subgroup A).map A.subtype
  let N := Subgroup.normalizer (H0 : Set (Perm X))
  obtain ⟨Q, hPQ⟩ := (P.isPGroup'.map A.subtype).exists_le_sylow
  have hQN : (Q : Subgroup (Perm X)) ≤ N :=
    CFSGAlternatingSylowAmbientNormalizer.sylow_le_normalizer P Q hPQ
  have hsmall : ∀ x, (CFSGNormalizerTranspositionClasses.pointClass N x).ncard ≤ 2 :=
    CFSGAlternatingNormalizerSmallClasses.class_card_le_two P hn
  let m := matching Q
  let C := Subgroup.centralizer ({m} : Set (Perm X))
  have hNC : N ≤ C := CFSGNormalizerMatchingCentralizer.le_matching_centralizer N hsmall Q hQN
  have hQC : (Q : Subgroup (Perm X)) ≤ C := hQN.trans hNC
  have hHC : H0 ≤ C := hPQ.trans hQC
  have hm2 : m ^ 2 = 1 := CFSGSymmetricSylowNormalizerStep.matching_square Q
  have hmne : m ≠ 1 := by
    intro he
    haveI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨a, b, hab⟩ := exists_pair_ne X
    have ha : matching Q a = a := by change m a = a; rw [he]; rfl
    have hb : matching Q b = b := by change m b = b; rw [he]; rfl
    exact hab (matching_fixedPoints_subsingleton Q ha hb)
  let phi := OnCycleFactors.toPermHom m
  have hphi : Function.Surjective phi := cycleAction_surjective m hm2
  have hker : IsPGroup 2 phi.ker := cycleAction_kernel_isPGroup m hm2
    (matching_fixedPoints_subsingleton Q)
  let Qc : Sylow 2 C := Q.subtype hQC
  have hkerle : phi.ker ≤ (Qc : Subgroup C) :=
    le_sup_right.trans (Qc.is_maximal'
      (Qc.isPGroup'.to_sup_of_normal_right hker) le_sup_left).le
  obtain ⟨t, htker, htodd⟩ := CFSGInvolutionCycleActionOddKernel.exists_odd_kernel m hm2 hmne
  have htQ : t ∈ Qc := hkerle htker
  have htphi : phi t = 1 := htker
  let sgn : C →* ℤˣ := Perm.sign.comp C.subtype
  have htsign : sgn t = -1 := by
    rcases Int.units_eq_one_or (sgn t) with hs | hs
    · exact False.elim (htodd (mem_alternatingGroup.mpr hs))
    · exact hs
  let H := H0.subgroupOf C
  have heven : H = (Qc : Subgroup C) ⊓ sgn.ker := by
    ext c
    change c.val ∈ H0 ↔ c.val ∈ Q ∧ Perm.sign c.val = 1
    exact CFSGAlternatingSylowEvenIntersection.mem_ambient_iff P Q hPQ c.val
  let R : Sylow 2 (Perm m.cycleFactorsFinset) := Qc.mapSurjective hphi
  have himage : H.map phi = (R : Subgroup (Perm m.cycleFactorsFinset)) := by
    have he := CFSGSignKernelImage.map_eq_map_inf_ker (Qc : Subgroup C) phi sgn t htQ htphi htsign
    rw [← heven] at he
    exact he.symm
  have hN : IsPGroup 2 (Subgroup.normalizer (H : Set C)) :=
    CFSGSymmetricImageNormalizer.normalizer_isPGroup H phi hker R himage
  have hsub : N.subgroupOf C = Subgroup.normalizer (H : Set C) :=
    Subgroup.subgroupOf_normalizer_eq hHC
  have hp := hN.map C.subtype
  rw [← hsub, Subgroup.map_subgroupOf_eq_of_le hNC] at hp
  exact hp

theorem normalizer_isPGroup {X : Type*} [Fintype X] [DecidableEq X]
    (P : Sylow 2 (alternatingGroup X)) (hn : 6 ≤ Nat.card X) :
    IsPGroup 2 (Subgroup.normalizer (P : Set (alternatingGroup X))) := by
  have hp := (ambient_normalizer_isPGroup P hn).comap_of_injective
    (alternatingGroup X).subtype (alternatingGroup X).subtype_injective
  apply hp.to_le
  rw [← Subgroup.map_le_iff_le_comap]
  exact Subgroup.le_normalizer_map (alternatingGroup X).subtype

theorem normalizer_eq_self {X : Type*} [Fintype X] [DecidableEq X]
    (P : Sylow 2 (alternatingGroup X)) (hn : 6 ≤ Nat.card X) :
    Subgroup.normalizer (P : Set (alternatingGroup X)) = P :=
  P.is_maximal' (normalizer_isPGroup P hn) Subgroup.le_normalizer

end SymmetricSubgroupAsymptotics.CFSGAlternatingSylowSelfNormalizer
