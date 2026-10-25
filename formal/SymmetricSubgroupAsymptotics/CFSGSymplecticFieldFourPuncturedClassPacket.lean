import SymmetricSubgroupAsymptotics.BinarySymmetricSquarePuncturedAnnihilatorIndex
import SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryRankTwoSharpIndex
import SymmetricSubgroupAsymptotics.CFSGSymplecticSmallClassBounds
import SymmetricSubgroupAsymptotics.CFSGSymplecticSharpComponentOrderCube

/-! The actual four-element-field C2 Siegel stabilizer retains its
prime-field kernel and projected GL2 subgroup. Its detecting dual orbit
omits zero, so binary quotient cardinality raises index18 to24. The
already checked class192 and outer6 bounds then pay the scaled packet. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticFieldFourPuncturedClassPacket
open PrimitiveSocleRawStructure CFSGReduction BinarySymmetricSquareAction
open CFSGSymplecticSerreMatrices CFSGSymplecticRankTwoSiegelEmbedding
open CFSGSymplecticRankTwoSiegelExtension CFSGSymplecticBinarySiegelStabilizerIndex

local instance (K : Type) [Field K] [CharP K 2] : Algebra (ZMod 2) K := ZMod.algebra K 2

private theorem semidirect_index_lower (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K=4) (M : Subgroup (Siegel K)) (t : K)
    (ht : SemidirectProduct.inl (Multiplicative.ofAdd (offDiagonal K t)) ∉ M) :
    24 ≤ M.index := by
  let J := kernelSubmodule K M
  let L := M.map SemidirectProduct.rightHom
  letI : Finite (Space (K := K) ⧸ J) := Finite.of_surjective J.mkQ J.mkQ_surjective
  letI : Module.Finite (ZMod 2) (Space (K := K) ⧸ J) := Module.Finite.of_finite
  have hJ : ∀ A ∈ L, ∀ S ∈ J, congruenceLinearMap A S ∈ J := by
    intro A hA S hS
    change Multiplicative.ofAdd S ∈ M.comap SemidirectProduct.inl at hS
    change congruenceAction K A (Multiplicative.ofAdd S) ∈ M.comap SemidirectProduct.inl
    exact AbelianSemidirectStabilizerIndex.action_mem_kernel_of_projected
      (congruenceAction K) M A hA (Multiplicative.ofAdd S) hS
  have hnot : coordinates (Pi.single (1 : Fin 3) t) ∉ J := ht
  have hb := BinarySymmetricSquarePuncturedAnnihilatorIndex.field_mul_square_sub_one_le_two_mul_punctured_quotient_index
    (F := ZMod 2) L J hJ t hnot
  have h18 : 18 ≤ (Nat.card (Space (K := K) ⧸ J)-1)*L.index := by
    norm_num only [hK,Nat.reduceSub,Nat.reducePow,Nat.reduceMul] at hb
    omega
  have hcard : Nat.card (Space (K := K) ⧸ J)=
      2^Module.finrank (ZMod 2) (Space (K := K) ⧸ J) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  rw [hcard] at h18
  have h24 := BinarySymmetricSquarePuncturedAnnihilatorIndex.twentyFour_le_binary_multiple
    (Module.finrank (ZMod 2) (Space (K := K) ⧸ J)) L.index
    (Nat.pos_of_ne_zero L.index_ne_zero_of_finite) h18
  rw [←hcard,quotient_card_eq_kernel_index K M] at h24
  exact h24.trans_eq (AbelianSemidirectStabilizerIndex.index_factor (congruenceAction K) M).symm

private theorem projective_index_lower (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K=4) [IsSimpleGroup (elementaryProjective K 2)]
    (H : Subgroup (elementaryProjective K 2)) (hH : H ≠ ⊤) : 24 ≤ H.index := by
  let u : Multiplicative (Space (K := K)) := Multiplicative.ofAdd (offDiagonal K 1)
  have hu : u ≠ 1 := by
    intro he
    apply offDiagonal_ne_zero K 1 one_ne_zero
    exact congrArg Multiplicative.toAdd he
  have hn : projectiveExtensionHom K (SemidirectProduct.inl u) ≠ 1 := by
    rw [projectiveExtensionHom_inl]
    intro he
    apply hu
    apply projectiveUpperHom_injective K
    exact he.trans (projectiveUpperHom K).map_one.symm
  obtain ⟨x,hx⟩ := CFSGConjugateSubgroupDegree.exists_moved_coset_of_ne_one H hH _ hn
  letI : MulAction (Siegel K) (elementaryProjective K 2 ⧸ H) :=
    MulAction.compHom _ (projectiveExtensionHom K)
  have hb := semidirect_index_lower K hK (MulAction.stabilizer (Siegel K) x) 1 hx
  have ho : (MulAction.stabilizer (Siegel K) x).index=Nat.card (MulAction.orbit (Siegel K) x) :=
    (Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (Siegel K) x)).symm
  rw [ho] at hb
  have hc := hb.trans (Nat.card_le_card_of_injective
    (fun y : MulAction.orbit (Siegel K) x => y.val) Subtype.val_injective)
  simpa only [Subgroup.index_eq_card] using hc

theorem typeC_field_four_index_lower (q : CFSG.PrimePower) (hq : q.order=4)
    [IsSimpleGroup (CFSG.Models.C 2 q)]
    (H : Subgroup (CFSG.Models.C 2 q)) (hH : H ≠ ⊤) : 24 ≤ H.index := by
  have hp : q.prime=2 :=
    (Nat.Prime.pow_inj' q.prime_isPrime Nat.prime_two q.exponent_pos.ne'
      (by decide : (2:ℕ) ≠ 0) (show q.prime^q.exponent=2^2 from hq)).1
  letI : CharP q.Field 2 := by rw [←hp]; infer_instance
  let e := serreProjectiveEquivElementaryProjective q.Field 1
  letI : IsSimpleGroup (elementaryProjective q.Field 2) := e.symm.isSimpleGroup
  have hmap : H.map e.toMonoidHom ≠ ⊤ := by
    intro ht
    apply hH
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
  have h := projective_index_lower q.Field (q.card_field.trans hq) (H.map e.toMonoidHom) hmap
  have hidx : (H.map e.toMonoidHom).index=H.index := H.index_map_equiv e
  rw [hidx] at h
  exact h

theorem scaled_class_cube_le_proper_index (q : CFSG.PrimePower) (hq : q.order=4)
    [IsSimpleGroup (CFSG.Models.C 2 q)] [Finite (CFSG.Models.C 2 q)]
    (H : Subgroup (CFSG.Models.C 2 q)) (hH : H ≠ ⊤) :
    25*(Nat.card (ConjClasses (CFSG.Models.C 2 q))*
      Nat.card (Outer (CFSG.Models.C 2 q)))^3 ≤ 3^H.index := by
  have hp : q.prime=2 ∧ q.exponent=2 :=
    Nat.Prime.pow_inj' q.prime_isPrime Nat.prime_two q.exponent_pos.ne'
      (by decide : (2:ℕ) ≠ 0) (show q.prime^q.exponent=2^2 from hq)
  letI : CharP q.Field 2 := by rw [←hp.1]; infer_instance
  let e := serreProjectiveEquivElementaryProjective q.Field 1
  have hquot : Nat.card (ConjClasses (elementaryProjective q.Field 2)) ≤
      Nat.card (ConjClasses (elementaryRootGroup q.Field 2)) :=
    Nat.card_le_card_of_surjective
      (ConjClasses.map (QuotientGroup.mk' (Subgroup.center (elementaryRootGroup q.Field 2))))
      (ConjClasses.map_surjective (QuotientGroup.mk'_surjective _))
  have hc : Nat.card (ConjClasses (CFSG.Models.C 2 q)) ≤ 192 :=
    (Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
      (ConjClasses.map_surjective e.symm.surjective)).trans
      (hquot.trans (CFSGSymplecticSmallClassBounds.four_rankTwo q.Field (q.card_field.trans hq)))
  have ho : Nat.card (Outer (CFSG.Models.C 2 q)) ≤ 6 := by
    simpa only [CFSGFiniteFieldAutomorphisms.primePower_card_ringAut q,hp.2] using
      typeC_outer_card_le 2 (by decide) q
  exact ((Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left (Nat.mul_le_mul hc ho) 3)).trans
    (by decide +kernel : 25*((192:ℕ)*6)^3 ≤ 3^24)).trans
      (Nat.pow_le_pow_right (by decide) (typeC_field_four_index_lower q hq H hH))

end SymmetricSubgroupAsymptotics.CFSGSymplecticFieldFourPuncturedClassPacket
