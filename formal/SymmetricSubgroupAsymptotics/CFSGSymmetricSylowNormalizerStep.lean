import SymmetricSubgroupAsymptotics.CFSGSymmetricSylowCanonicalMatching
import SymmetricSubgroupAsymptotics.CFSGInvolutionCentralizerTwoKernel

/-! The actual smaller-degree step for symmetric Sylow normalizers. The
canonical matching centralizer maps onto the symmetric group on its
two-cycles, with two-group kernel. Self-normalization in that smaller
symmetric group forces self-normalization upstairs by Sylow maximality. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGSymmetricSylowNormalizerStep
open Equiv Equiv.Perm
open CFSGSymmetricSylowCanonicalMatching CFSGInvolutionCentralizerTwoKernel
variable {X : Type*} [Fintype X] [DecidableEq X] (P : Sylow 2 (Perm X))

theorem matching_square : matching P ^ 2 = 1 := by
  apply Perm.ext
  intro x
  change partner P (partner P x) = x
  exact partner_involutive P x

theorem normalizer_le_matching_centralizer :
    Subgroup.normalizer (P : Set (Perm X)) ≤
      Subgroup.centralizer ({matching P} : Set (Perm X)) := by
  intro g hg
  apply Subgroup.mem_centralizer_iff.mpr
  intro t ht
  have he : t = matching P := Set.mem_singleton_iff.mp ht
  subst t
  apply Perm.ext
  intro x
  change partner P (g x) = g (partner P x)
  exact (normalizer_preserves_partner P g hg x).symm

theorem normalizer_eq_self_of_cycle_action
    (hrec : ∀ Q : Sylow 2 (Perm (matching P).cycleFactorsFinset),
      Subgroup.normalizer (Q : Set (Perm (matching P).cycleFactorsFinset)) = Q) :
    Subgroup.normalizer (P : Set (Perm X)) = P := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C := Subgroup.centralizer ({matching P} : Set (Perm X))
  have hNC : Subgroup.normalizer (P : Set (Perm X)) ≤ C :=
    normalizer_le_matching_centralizer P
  have hPC : (P : Subgroup (Perm X)) ≤ C := Subgroup.le_normalizer.trans hNC
  let Q : Sylow 2 C := P.subtype hPC
  let phi := OnCycleFactors.toPermHom (matching P)
  have hphi : Function.Surjective phi := cycleAction_surjective _ (matching_square P)
  let R : Sylow 2 (Perm (matching P).cycleFactorsFinset) := Q.mapSurjective hphi
  have hker : IsPGroup 2 phi.ker :=
    cycleAction_kernel_isPGroup _ (matching_square P) (matching_fixedPoints_subsingleton P)
  have hrecR := hrec R
  have hle : Subgroup.normalizer (Q : Set C) ≤ (R : Subgroup _).comap phi := by
    rw [← Subgroup.map_le_iff_le_comap]
    change (Subgroup.normalizer (Q : Set C)).map phi ≤ Q.toSubgroup.map phi
    have hrecR' : Subgroup.normalizer (Q.toSubgroup.map phi : Set _) =
        Q.toSubgroup.map phi := hrecR
    exact (Subgroup.le_normalizer_map phi).trans_eq hrecR'
  have hqN : IsPGroup 2 (Subgroup.normalizer (Q : Set C)) :=
    (R.isPGroup'.comap_of_ker_isPGroup phi hker).to_le hle
  have hN : IsPGroup 2 (Subgroup.normalizer (P : Set (Perm X))) := by
    have he : (Subgroup.normalizer (P : Set (Perm X))).subgroupOf C =
        Subgroup.normalizer (Q : Set C) := Subgroup.subgroupOf_normalizer_eq hPC
    have hp := hqN.map C.subtype
    rw [← he, Subgroup.map_subgroupOf_eq_of_le hNC] at hp
    exact hp
  exact P.is_maximal' hN Subgroup.le_normalizer

theorem matching_cycle_degree_lt (hpos : 0 < Fintype.card X) :
    Fintype.card (matching P).cycleFactorsFinset < Fintype.card X := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htype := cycleType_of_pow_prime_eq_one (matching_square P)
  have hsum := sum_cycleType (matching P)
  rw [htype, Multiset.sum_replicate, nsmul_eq_mul] at hsum
  have hcount : (matching P).cycleType.card =
      Fintype.card (matching P).cycleFactorsFinset := by
    simp only [cycleType_def, Multiset.card_map, Fintype.card_coe]
    rfl
  rw [hcount] at hsum
  norm_num only [Nat.cast_id] at hsum
  have hle := (matching P).support.card_le_univ
  omega

end SymmetricSubgroupAsymptotics.CFSGSymmetricSylowNormalizerStep
