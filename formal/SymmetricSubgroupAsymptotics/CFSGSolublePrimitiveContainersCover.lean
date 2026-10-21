import SymmetricSubgroupAsymptotics.CFSGSolublePrimitiveContainersMenu
import SymmetricSubgroupAsymptotics.CFSGSolublePrimitiveContainersProfile
import SymmetricSubgroupAsymptotics.PrimitiveAffineSolubleDerivedTarget
import SymmetricSubgroupAsymptotics.PrimitiveAffineDimensionOrder
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawONanScottProof

/-! The finite affine menu covers every actual faithful soluble primitive
action. Only proved affine/regular-normal structure is used. The result is
literal labelled subgroup containment after recording a point permutation. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.CFSGSolublePrimitiveContainers

theorem soluble_primitive_profile (G X : Type) [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] [MulAction.IsPreprimitive G X]
    [Nontrivial X] [IsSolvable G] : Nonempty (PrimitiveAffineProfile G X) := by
  cases Classical.choice (PrimitiveSocleRawStructure.publishedONanScottStructure G X) with
  | inr P => exact ⟨P⟩
  | inl D =>
    let i : Fin D.factorCount := ⟨0, D.factorCount_pos⟩
    let f : finiteGroupSocle G →* D.Simple :=
      (Pi.evalMonoidHom (fun _ : Fin D.factorCount => D.Simple) i).comp
        D.socleEquiv.toMonoidHom
    have hf : Function.Surjective f := by
      intro s
      exact ⟨D.socleEquiv.symm (fun _ => s), by simp [f]⟩
    have hs : IsSolvable D.Simple := solvable_of_surjective hf
    exact (D.noncommutative ⟨⟨IsSimpleGroup.comm_iff_isSolvable.mpr hs⟩⟩).elim

theorem profile_translation_parameter {G X : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] [Nontrivial X] (P : PrimitiveAffineProfile G X)
    (hprimitive : MulAction.IsPreprimitive G X) (x : X) (n : ℕ)
    (hcard : Nat.card X = n) :
    ∃ Q : TranslationParameter n, Nonempty (P.V ≃* CanonicalTranslation Q) := by
  let C := P.elementaryChart hprimitive
  letI solublePrimitiveCover_prime : Fact P.p.Prime := C.primeFact
  letI solublePrimitiveCover_finiteModule : Finite C.V :=
    Finite.of_injective (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v))
      C.equiv.symm.injective
  have hdegree : n = P.p ^ C.d :=
    hcard.symm.trans (P.degree_eq_prime_pow_finrank C.equiv x)
  have hpbound : P.p ≤ n := by
    rw [hdegree]
    simpa only [pow_one] using Nat.pow_le_pow_right P.p_prime.pos C.d_pos
  have hdbound : C.d ≤ Nat.log2 n := by
    rw [Nat.log2_eq_log_two]
    apply Nat.le_log_of_pow_le (by decide : 1 < (2 : ℕ))
    rw [hdegree]
    exact Nat.pow_le_pow_left P.p_prime.two_le C.d
  let Q : TranslationParameter n := {
    prime := ⟨P.p, by omega⟩
    dimension := ⟨C.d, by unfold logSize; omega⟩
    prime_isPrime := P.p_prime
    dimension_pos := C.d_pos
    degree_eq := hdegree.symm }
  exact ⟨Q, ⟨C.standardEquiv⟩⟩

theorem primitive_menu_covers (n : ℕ) (U : Subgroup (Equiv.Perm (Fin n)))
    [Nontrivial (Fin n)] [MulAction.IsPreprimitive U (Fin n)] [IsSolvable U] :
    ∃ i : PrimitiveIndex n, U ≤ primitiveEnvelope i := by
  obtain ⟨P⟩ := soluble_primitive_profile U (Fin n)
  let x : Fin n := Classical.choice inferInstance
  obtain ⟨Q, ⟨a⟩⟩ := profile_translation_parameter P inferInstance x n (Nat.card_fin n)
  let H := profileComplement P x a
  have hH : IsSolvable H := profileComplement_soluble P x a
  let label : Equiv.Perm (Fin n) :=
    (standardPoints Q).symm.trans (profilePoints P x a)
  let i : PrimitiveIndex n := ⟨Q, ⟨⟨H, hH⟩, label⟩⟩
  refine ⟨i, ?_⟩
  have hpoints : (standardPoints Q).trans label = profilePoints P x a := by
    ext t
    simp only [label, Equiv.trans_apply, Equiv.symm_apply_apply]
  change U ≤ labelledEnvelope (CanonicalTranslation Q) H ((standardPoints Q).trans label)
  rw [hpoints]
  intro g hg
  exact profile_range_le_labelledEnvelope P x a ⟨⟨g, hg⟩, rfl⟩

end SymmetricSubgroupAsymptotics.CFSGSolublePrimitiveContainers
