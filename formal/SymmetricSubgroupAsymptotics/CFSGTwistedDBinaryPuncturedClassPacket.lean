import SymmetricSubgroupAsymptotics.NondegenerateBilinearPuncturedAnnihilatorOrbitIndex
import SymmetricSubgroupAsymptotics.CFSGTwistedDPointRadicalIndex
import SymmetricSubgroupAsymptotics.CFSGTwistedDBinaryIsometryClassBound
import SymmetricSubgroupAsymptotics.CFSGTwistedDOuterCardinality

/-! The literal binary minus-D4 point radical has nonzero natural
orbits of size at least24. Removing zero from the SAME annihilator,
and retaining the SAME projected subgroup, raises the proper-index
bound to32. The existing class3072 and outer8 bounds then suffice. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDBinaryPuncturedClassPacket
open PrimitiveSocleRawStructure CFSGTwistedDFixedQuadraticSpace
open CFSGTwistedDFixedQuadraticAction CFSGTwistedDFixedQuadraticNondegenerate
open CFSGTwistedDRelativeElementaryGroup CFSGTwistedDRelativeProjectiveModel
open CFSGTwistedDPointRadicalHom CFSGTwistedDPointRadicalExtension
open CFSGTwistedDPointRadicalStabilizerIndex CFSGTwistedDAllNormOrbitCardinality
open CFSGTwistedDSingularDimensionBound CFSGTwistedA2FixedField

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance (q : CFSG.PrimePower) [CharP (fixedField q) 2] :
    Algebra (ZMod 2) (fixedField q) := ZMod.algebra (fixedField q) 2
local instance (q : CFSG.PrimePower) [CharP (fixedField q) 2] (n : ℕ) :
    Module (ZMod 2) (fixedSpace n q) :=
  Module.restrictScalars (ZMod 2) (fixedField q) (fixedSpace n q)
local instance (q : CFSG.PrimePower) [CharP (fixedField q) 2] (n : ℕ) :
    IsScalarTower (ZMod 2) (fixedField q) (fixedSpace n q) :=
  IsScalarTower.restrictScalars (ZMod 2) (fixedField q) (fixedSpace n q)

private theorem semidirect_index_lower (q : CFSG.PrimePower) (hq : q.order=2)
    [CharP (fixedField q) 2] (M : Subgroup (PointParabolic 0 q))
    (z : fixedSpace 1 q) (hz : SemidirectProduct.inl (Multiplicative.ofAdd z) ∉ M) :
    32 ≤ M.index := by
  let J := kernelSubmodule 0 q 2 M
  let L := M.map SemidirectProduct.rightHom
  let ρ := fixedLinearHom 1 q
  let Q := fixedQuadraticForm 1 q
  letI : Finite (fixedSpace 1 q) := Finite.of_injective
    (fun v : fixedSpace 1 q => v.val) Subtype.val_injective
  letI : Finite (fixedSpace 1 q ⧸ J) := Finite.of_surjective J.mkQ J.mkQ_surjective
  letI : Module.Finite (ZMod 2) (fixedSpace 1 q ⧸ J) := Module.Finite.of_finite
  have hJ : ∀ g ∈ L, ∀ v ∈ J,
      FiniteFieldFunctionalOrbitTransfer.restrictedRepresentation (F := ZMod 2) ρ g v ∈ J := by
    intro g hg v hv
    change Multiplicative.ofAdd v ∈ M.comap SemidirectProduct.inl at hv
    change tailAction 1 q g (Multiplicative.ofAdd v) ∈ M.comap SemidirectProduct.inl
    exact AbelianSemidirectStabilizerIndex.action_mem_kernel_of_projected
      (tailAction 1 q) M g hg (Multiplicative.ofAdd v) hv
  have hρ : ∀ g : relativeRootGroup 1 q, ∀ v w : fixedSpace 1 q,
      Q.polarBilin (ρ g v) (ρ g w)=Q.polarBilin v w := by
    intro g v w
    exact QuadraticHyperbolicRadicalHom.polar_preserved Q (ρ g)
      (fixedLinearHom_preserves_Q 1 q g) v w
  have hlow := NondegenerateBilinearPuncturedAnnihilatorOrbitIndex.natural_orbit_lower_le_punctured_quotient_card_mul_index
    Q.polarBilin (fixedQuadraticForm_nondegenerate 1 q) ρ hρ 24
    (fun v hv => by simpa only [hq] using norm_slice_le_vectorOrbit 0 q v hv) L J hJ z hz
  have hcard : Nat.card (fixedSpace 1 q ⧸ J)=
      2^Module.finrank (ZMod 2) (fixedSpace 1 q ⧸ J) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  rw [hcard] at hlow
  have hbinary := NondegenerateBilinearPuncturedAnnihilatorOrbitIndex.thirtyTwo_le_binary_multiple
    (Module.finrank (ZMod 2) (fixedSpace 1 q ⧸ J)) L.index
    (Nat.pos_of_ne_zero L.index_ne_zero_of_finite) hlow
  rw [←hcard,quotient_card_eq_kernel_index 0 q 2 M] at hbinary
  exact hbinary.trans_eq (AbelianSemidirectStabilizerIndex.index_factor (tailAction 1 q) M).symm

private theorem projective_index_lower (q : CFSG.PrimePower) (hq : q.order=2)
    [IsSimpleGroup (relativeRootGroup 2 q ⧸ Subgroup.center (relativeRootGroup 2 q))]
    (H : Subgroup (relativeRootGroup 2 q ⧸ Subgroup.center (relativeRootGroup 2 q)))
    (hH : H ≠ ⊤) : 32 ≤ H.index := by
  letI : Finite (relativeRootGroup 2 q ⧸ Subgroup.center (relativeRootGroup 2 q)) :=
    Finite.of_surjective (QuotientGroup.mk' (Subgroup.center (relativeRootGroup 2 q)))
      (QuotientGroup.mk'_surjective _)
  have hp : q.prime=2 :=
    (Nat.Prime.pow_inj' q.prime_isPrime Nat.prime_two q.exponent_pos.ne'
      (by decide : (1:ℕ) ≠ 0) (show q.prime^q.exponent=2^1 from hq)).1
  letI : CharP (fixedField q) q.prime :=
    (fixedField q).subtype.charP (fixedField q).subtype.injective q.prime
  letI : CharP (fixedField q) 2 := Eq.mp
    (congrArg (fun p : ℕ => CharP (fixedField q) p) hp)
    (inferInstance : CharP (fixedField q) q.prime)
  let z := firstAxis 1 q
  have hz : z ≠ 0 := firstAxis_nonzero 1 q
  let u : Multiplicative (fixedSpace 1 q) := Multiplicative.ofAdd z
  have hu : u ≠ 1 := fun he => hz (congrArg Multiplicative.toAdd he)
  have hn : projectiveExtensionHom 1 q (SemidirectProduct.inl u) ≠ 1 := by
    rw [projectiveExtensionHom_inl]
    intro he
    apply hu
    apply projectiveRadicalHom_injective 1 q
    exact he.trans (projectiveRadicalHom 1 q).map_one.symm
  obtain ⟨x,hx⟩ := CFSGConjugateSubgroupDegree.exists_moved_coset_of_ne_one H hH _ hn
  letI : MulAction (PointParabolic 0 q)
      ((relativeRootGroup 2 q ⧸ Subgroup.center (relativeRootGroup 2 q)) ⧸ H) :=
    MulAction.compHom _ (projectiveExtensionHom 1 q)
  have hb := semidirect_index_lower q hq
    (MulAction.stabilizer (PointParabolic 0 q) x) z hx
  have ho : (MulAction.stabilizer (PointParabolic 0 q) x).index=
      Nat.card (MulAction.orbit (PointParabolic 0 q) x) :=
    (Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (PointParabolic 0 q) x)).symm
  rw [ho] at hb
  have hc := hb.trans (Nat.card_le_card_of_injective
    (fun y : MulAction.orbit (PointParabolic 0 q) x => y.val) Subtype.val_injective)
  simpa only [Subgroup.index_eq_card] using hc

theorem typeTwistedD_binary_rank_four_index_lower (q : CFSG.PrimePower) (hq : q.order=2)
    [IsSimpleGroup (CFSG.Models.TwistedD 4 q)]
    (H : Subgroup (CFSG.Models.TwistedD 4 q)) (hH : H ≠ ⊤) : 32 ≤ H.index := by
  let e := originalRelativeProjectiveEquiv 0 q
  letI : IsSimpleGroup (relativeRootGroup 2 q ⧸ Subgroup.center (relativeRootGroup 2 q)) :=
    e.symm.isSimpleGroup
  have hmap : H.map e.toMonoidHom ≠ ⊤ := by
    intro ht
    apply hH
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
  have h := projective_index_lower q hq (H.map e.toMonoidHom) hmap
  have hidx : (H.map e.toMonoidHom).index=H.index := H.index_map_equiv e
  rw [hidx] at h
  exact h

theorem scaled_class_cube_le_proper_index (q : CFSG.PrimePower) (hq : q.order=2)
    [IsSimpleGroup (CFSG.Models.TwistedD 4 q)] [Finite (CFSG.Models.TwistedD 4 q)]
    (hn : ¬IsMulCommutative (CFSG.Models.TwistedD 4 q))
    (H : Subgroup (CFSG.Models.TwistedD 4 q)) (hH : H ≠ ⊤) :
    25*(Nat.card (ConjClasses (CFSG.Models.TwistedD 4 q))*
      Nat.card (Outer (CFSG.Models.TwistedD 4 q)))^3 ≤ 3^H.index := by
  have he : q.exponent=1 :=
    (Nat.Prime.pow_inj' q.prime_isPrime Nat.prime_two q.exponent_pos.ne'
      (by decide : (1:ℕ) ≠ 0) (show q.prime^q.exponent=2^1 from hq)).2
  have hc := CFSGTwistedDBinaryIsometryClassBound.original_class_card_le q hq
  have ho : Nat.card (Outer (CFSG.Models.TwistedD 4 q)) ≤ 8 := by
    simpa only [he,mul_one] using
      CFSGTwistedDOuterCardinality.original_outer_card_le_eight_exponent 0 q hn
  exact ((Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left (Nat.mul_le_mul hc ho) 3)).trans
    (by decide +kernel : 25*((3072:ℕ)*8)^3 ≤ 3^32)).trans
      (Nat.pow_le_pow_right (by decide) (typeTwistedD_binary_rank_four_index_lower q hq H hH))

end SymmetricSubgroupAsymptotics.CFSGTwistedDBinaryPuncturedClassPacket
