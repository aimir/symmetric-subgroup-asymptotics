import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopTowerOuterNestedQuotient

/-!
# The fixed direct-omega lift in a two-frame pair tower

The coupled trivial-row argument must lift the fixed part of the direct
kernel omega, rather than the whole omega module.  In the original quotient
this lift is intrinsic: it is the intersection of the ambient omega subgroup
with the center.  This file identifies that literal subgroup with the fixed
space of the omega conjugation representation and pulls it back to the
original pair action.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoPairTopTowerRealization

variable {s t : ℕ} {D : DegreeTwoPairTopFiniteInterface t}
  {p : PreE7PairActionClass s}
  (R : DegreeTwoPairTopTowerRealization D p)

/-- The actual central part of the direct-kernel omega subgroup in the
original quotient. -/
def rawKernelOmegaFixedLift
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Subgroup (preE7PairAction s p ⨸ N.1) :=
  R.rawKernelOmegaLift N ⊓ Subgroup.center (preE7PairAction s p ⨸ N.1)

instance rawKernelOmegaFixedLift_normal
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (R.rawKernelOmegaFixedLift N).Normal :=
  inferInstance

/-- Pull the fixed omega lift back to the original action.  This is the
normal subgroup denoted `D` in the three-layer coupled-head argument. -/
def rawKernelOmegaFixedOriginalPreimage
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Subgroup (preE7PairAction s p) := by
  letI : N.1.Normal := N.2
  exact (R.rawKernelOmegaFixedLift N).comap (QuotientGroup.mk' N.1)

instance rawKernelOmegaFixedOriginalPreimage_normal
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (R.rawKernelOmegaFixedOriginalPreimage N).Normal := by
  letI : N.1.Normal := N.2
  exact Subgroup.Normal.comap inferInstance (QuotientGroup.mk' N.1)

theorem originalNormal_le_rawKernelOmegaFixedOriginalPreimage
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    N.1 ≤ R.rawKernelOmegaFixedOriginalPreimage N := by
  intro u hu
  change QuotientGroup.mk' N.1 u ∈ R.rawKernelOmegaFixedLift N
  rw [QuotientGroup.eq_one_iff.mpr hu]
  exact Subgroup.one_mem _

/-- Image of the fixed omega lift in the intermediate pair top. -/
def rawKernelOmegaFixedTopImage
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Subgroup (R.frame.top.range ⨸ R.outerTopNormal N.1) :=
  (R.rawKernelOmegaFixedLift N).map (R.outerQuotientMap N)

instance rawKernelOmegaFixedTopImage_normal
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (R.rawKernelOmegaFixedTopImage N).Normal :=
  Subgroup.Normal.map inferInstance _ (R.outerQuotientMap_surjective N)

theorem rawKernelOmegaFixedTopImage_le_innerKernel
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    R.rawKernelOmegaFixedTopImage N ≤ (R.innerQuotientMap N).ker := by
  rintro y ⟨x, hx, rfl⟩
  apply MonoidHom.mem_ker.mpr
  simpa only [rawQuotientMap, MonoidHom.comp_apply] using
    MonoidHom.mem_ker.mp hx.1.1

/-- Pull the fixed intermediate image back before the second quotient. -/
def rawKernelOmegaFixedIntermediatePreimage
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Subgroup R.frame.top.range := by
  letI : N.1.Normal := N.2
  letI : (R.outerTopNormal N.1).Normal := R.outerTopNormal_normal N.1
  exact (R.rawKernelOmegaFixedTopImage N).comap
    (QuotientGroup.mk' (R.outerTopNormal N.1))

/-- The fixed intermediate pullback is exactly the first-top image of the
fixed original pullback. -/
theorem rawKernelOmegaFixedIntermediatePreimage_eq_map
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    R.rawKernelOmegaFixedIntermediatePreimage N =
      (R.rawKernelOmegaFixedOriginalPreimage N).map
        R.frame.top.rangeRestrict := by
  letI : N.1.Normal := N.2
  letI : (R.outerTopNormal N.1).Normal := R.outerTopNormal_normal N.1
  ext y
  constructor
  · intro hy
    change QuotientGroup.mk' (R.outerTopNormal N.1) y ∈
      (R.rawKernelOmegaFixedLift N).map (R.outerQuotientMap N) at hy
    obtain ⟨q, hq, hqy⟩ := hy
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective N.1 q
    rw [R.outerQuotientMap_apply] at hqy
    have hdiv : R.frame.top.rangeRestrict u / y ∈
        R.outerTopNormal N.1 :=
      QuotientGroup.eq_iff_div_mem.mp hqy
    obtain ⟨n, hn, hntop⟩ := hdiv
    have hnFixed : n ∈ R.rawKernelOmegaFixedOriginalPreimage N :=
      R.originalNormal_le_rawKernelOmegaFixedOriginalPreimage N hn
    refine ⟨u * n⁻¹,
      (R.rawKernelOmegaFixedOriginalPreimage N).mul_mem hq
        ((R.rawKernelOmegaFixedOriginalPreimage N).inv_mem hnFixed), ?_⟩
    rw [map_mul, map_inv, hntop]
    group
  · rintro ⟨u, hu, rfl⟩
    change QuotientGroup.mk' (R.outerTopNormal N.1)
        (R.frame.top.rangeRestrict u) ∈
      (R.rawKernelOmegaFixedLift N).map (R.outerQuotientMap N)
    exact ⟨QuotientGroup.mk' N.1 u, hu, rfl⟩

theorem outerTopNormal_le_rawKernelOmegaFixedIntermediatePreimage
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    R.outerTopNormal N.1 ≤ R.rawKernelOmegaFixedIntermediatePreimage N := by
  rw [R.rawKernelOmegaFixedIntermediatePreimage_eq_map N]
  exact Subgroup.map_mono
    (R.originalNormal_le_rawKernelOmegaFixedOriginalPreimage N)

instance rawKernelOmegaFixedIntermediatePreimage_normal
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (R.rawKernelOmegaFixedIntermediatePreimage N).Normal := by
  letI : N.1.Normal := N.2
  letI : (R.outerTopNormal N.1).Normal := R.outerTopNormal_normal N.1
  exact Subgroup.Normal.comap inferInstance
    (QuotientGroup.mk' (R.outerTopNormal N.1))

/-- A fixed omega vector gives a central element of the original quotient.
The statement keeps the concrete omega embedding visible for later
coordinate calculations. -/
theorem binaryCentralOmegaEmbedding_mem_center_of_fixed
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal})
    (z : binaryCentralOmega (R.rawQuotientMap N).ker)
    (hz : Additive.ofMul z ∈
      (binaryKernelOmegaConjugationRepresentation
        (R.rawQuotientMap N)).invariants) :
    (binaryCentralOmegaEmbedding z : preE7PairAction s p ⨸ N.1) ∈
      Subgroup.center (preE7PairAction s p ⨸ N.1) := by
  apply Subgroup.mem_center_iff.mpr
  intro q
  have hfix := hz q
  change Additive.ofMul
      (binaryKernelOmegaConjugateOmega (R.rawQuotientMap N) q z) =
        Additive.ofMul z at hfix
  have hconj := congrArg
    (fun w : Additive (binaryCentralOmega (R.rawQuotientMap N).ker) ↦
      (binaryCentralOmegaEmbedding w.toMul :
        preE7PairAction s p ⨸ N.1)) hfix
  rw [binaryKernelOmegaConjugate_val] at hconj
  have hright := congrArg
    (fun x : preE7PairAction s p ⨸ N.1 ↦ x * q) hconj
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hright

/-- Conversely, an omega element central in the original quotient is fixed
by the whole omega conjugation representation. -/
theorem fixed_of_binaryCentralOmegaEmbedding_mem_center
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal})
    (z : binaryCentralOmega (R.rawQuotientMap N).ker)
    (hz : (binaryCentralOmegaEmbedding z : preE7PairAction s p ⨸ N.1) ∈
      Subgroup.center (preE7PairAction s p ⨸ N.1)) :
    Additive.ofMul z ∈
      (binaryKernelOmegaConjugationRepresentation
        (R.rawQuotientMap N)).invariants := by
  intro q
  apply Additive.toMul.injective
  apply binaryCentralOmegaEmbedding_injective
  apply Subtype.ext
  rw [binaryKernelOmegaConjugate_val]
  have hc := Subgroup.mem_center_iff.mp hz q
  calc
    q * (binaryCentralOmegaEmbedding z :
        preE7PairAction s p ⨸ N.1) * q⁻¹ =
        (binaryCentralOmegaEmbedding z :
          preE7PairAction s p ⨸ N.1) * q * q⁻¹ := by rw [hc]
    _ = (binaryCentralOmegaEmbedding z :
          preE7PairAction s p ⨸ N.1) := by simp

/-- The underlying additive group of the fixed omega lift is elementary
binary, because it is contained in the ambient omega subgroup. -/
instance rawKernelOmegaFixedLift_module
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Module (ZMod 2) (Additive (R.rawKernelOmegaFixedLift N)) :=
  AddCommGroup.zmodModule (n := 2) (fun x ↦ by
    apply Additive.toMul.injective
    apply Subtype.ext
    change (x.toMul.1 : preE7PairAction s p ⨸ N.1) ^ 2 = 1
    exact x.toMul.2.1.2.2.2)

/-- Fixed vectors in raw omega are exactly the additive form of the literal
central omega lift. -/
noncomputable def rawKernelOmegaInvariantsEquivFixedLift
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (binaryKernelOmegaConjugationRepresentation
        (R.rawQuotientMap N)).invariants ≃ₗ[ZMod 2]
      Additive (R.rawKernelOmegaFixedLift N) where
  toFun v := Additive.ofMul
    ⟨(R.rawKernelOmegaEquiv N v.1.toMul :
        R.rawKernelOmegaLift N).1,
      (R.rawKernelOmegaEquiv N v.1.toMul).2,
      by
        rw [R.rawKernelOmegaEquiv_val N]
        exact R.binaryCentralOmegaEmbedding_mem_center_of_fixed
          N v.1.toMul v.2⟩
  invFun z :=
    let omega := (R.rawKernelOmegaEquiv N).symm
      ⟨z.toMul.1, z.toMul.2.1⟩
    ⟨Additive.ofMul omega, by
      apply R.fixed_of_binaryCentralOmegaEmbedding_mem_center N omega
      rw [← R.rawKernelOmegaEquiv_val N omega]
      have he := congrArg Subtype.val
        ((R.rawKernelOmegaEquiv N).apply_symm_apply
          ⟨z.toMul.1, z.toMul.2.1⟩)
      exact he.symm ▸ z.toMul.2.2⟩
  left_inv v := by
    apply Subtype.ext
    apply Additive.toMul.injective
    exact (R.rawKernelOmegaEquiv N).symm_apply_apply v.1.toMul
  right_inv z := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg Subtype.val
      ((R.rawKernelOmegaEquiv N).apply_symm_apply
        ⟨z.toMul.1, z.toMul.2.1⟩)
  map_add' v w := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg Subtype.val
      (map_mul (R.rawKernelOmegaEquiv N) v.1.toMul w.1.toMul)
  map_smul' c v := by
    fin_cases c <;>
      simp only [zero_smul, one_smul, map_zero, map_one]

/-- Project the literal fixed lift onto the second pair kernel. -/
def rawKernelOmegaFixedProjection
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    R.rawKernelOmegaFixedLift N →* (R.innerQuotientMap N).ker where
  toFun z := ⟨R.outerQuotientMap N z.1, by
    apply MonoidHom.mem_ker.mpr
    simpa only [rawQuotientMap, MonoidHom.comp_apply] using
      MonoidHom.mem_ker.mp z.2.1.1⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x.1 y.1)

@[simp] theorem rawKernelOmegaFixedProjection_apply
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal})
    (z : R.rawKernelOmegaFixedLift N) :
    ((R.rawKernelOmegaFixedProjection N z : (R.innerQuotientMap N).ker) :
        R.frame.top.range ⨸ R.outerTopNormal N.1) =
      R.outerQuotientMap N z.1 :=
  rfl

theorem rawKernelOmegaFixedProjection_range_eq
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (R.rawKernelOmegaFixedProjection N).range =
      (R.rawKernelOmegaFixedTopImage N).subgroupOf
        (R.innerQuotientMap N).ker := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, z.2, rfl⟩
  · rintro ⟨z, hz, hzy⟩
    exact ⟨⟨z, hz⟩, Subtype.ext hzy⟩

/-- Actual second-section coordinates of the fixed intermediate image. -/
def fixedOmegaInnerSubrepresentation
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Subrepresentation (R.innerSectionModule N).ρ :=
  (R.innerSectionModuleChart N).normalSubrepresentation
    (R.innerQuotientMap N) (R.innerQuotientMap_surjective N)
    (R.innerSectionModule N) (R.rawKernelOmegaFixedTopImage N)

/-- Additive coordinates for the fixed projection in the actual second
section module. -/
noncomputable def rawKernelOmegaFixedInnerSectionMap
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Additive (R.rawKernelOmegaFixedLift N) →ₗ[ZMod 2]
      R.innerSectionModule N :=
  (((R.innerSectionModuleChart N).equiv.symm.toMonoidHom.comp
    (R.rawKernelOmegaFixedProjection N)).toAdditive).toZModLinearMap 2

@[simp] theorem rawKernelOmegaFixedInnerSectionMap_apply
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal})
    (z : R.rawKernelOmegaFixedLift N) :
    R.rawKernelOmegaFixedInnerSectionMap N (Additive.ofMul z) =
      ((R.innerSectionModuleChart N).kernelCoordinates
        (R.innerQuotientMap N) (R.innerSectionModule N)
        (R.rawKernelOmegaFixedProjection N z)).toAdd :=
  rfl

theorem rawKernelOmegaFixedInnerSectionMap_range_eq
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    LinearMap.range (R.rawKernelOmegaFixedInnerSectionMap N) =
      (R.fixedOmegaInnerSubrepresentation N).toSubmodule := by
  let E := R.innerSectionModuleChart N
  let L := (R.rawKernelOmegaFixedTopImage N).subgroupOf
    (R.innerQuotientMap N).ker
  have hker : (E.kernelCoordinates
      (R.innerQuotientMap N) (R.innerSectionModule N)).ker ≤ L := by
    intro x hx
    have hx1 : x = 1 := by
      apply E.equiv.symm.injective
      exact (MonoidHom.mem_ker.mp hx).trans
        (map_one E.equiv.symm).symm
    subst x
    exact Subgroup.one_mem _
  ext v
  constructor
  · rintro ⟨z, rfl⟩
    change ((E.kernelCoordinates
      (R.innerQuotientMap N) (R.innerSectionModule N)
      (R.rawKernelOmegaFixedProjection N z.toMul)).toAdd) ∈
        E.normalSpace (R.innerQuotientMap N)
          (R.innerSectionModule N) L
    apply (sectionSubgroupImage_mem_iff
      (E.kernelCoordinates (R.innerQuotientMap N)
        (R.innerSectionModule N)) L hker
      (R.rawKernelOmegaFixedProjection N z.toMul)).2
    rw [← R.rawKernelOmegaFixedProjection_range_eq N]
    exact ⟨z.toMul, rfl⟩
  · intro hv
    let y : (R.innerQuotientMap N).ker :=
      E.equiv (Multiplicative.ofAdd v)
    have hcoord : (E.kernelCoordinates
        (R.innerQuotientMap N) (R.innerSectionModule N) y).toAdd = v := by
      change (E.equiv.symm (E.equiv (Multiplicative.ofAdd v))).toAdd = v
      rw [E.equiv.symm_apply_apply]
      rfl
    have hy : y ∈ L := by
      apply (sectionSubgroupImage_mem_iff
        (E.kernelCoordinates (R.innerQuotientMap N)
          (R.innerSectionModule N)) L hker y).1
      change v ∈ E.normalSpace (R.innerQuotientMap N)
        (R.innerSectionModule N) L at hv
      rwa [hcoord]
    have hyrange : y ∈ (R.rawKernelOmegaFixedProjection N).range := by
      rw [R.rawKernelOmegaFixedProjection_range_eq N]
      exact hy
    obtain ⟨z, hz⟩ := hyrange
    refine ⟨Additive.ofMul z, ?_⟩
    rw [R.rawKernelOmegaFixedInnerSectionMap_apply N z, hz, hcoord]

theorem rawKernelOmegaFixedOriginalPreimage_commutator_mem_right
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal})
    (u v : preE7PairAction s p)
    (hv : v ∈ R.rawKernelOmegaFixedOriginalPreimage N) :
    u⁻¹ * v * u * v⁻¹ ∈ N.1 := by
  letI : N.1.Normal := N.2
  apply (QuotientGroup.eq_one_iff _).mp
  simp only [map_mul, map_inv]
  have hcentral : Commute (QuotientGroup.mk' N.1 u)
      (QuotientGroup.mk' N.1 v) :=
    (Subgroup.mem_center_iff.mp hv.2.2
      (QuotientGroup.mk' N.1 u)).symm
  rw [hcentral.eq]
  group

/-- A fixed pullback element commutes modulo the denominator with every
element of the original action. -/
theorem rawKernelOmegaFixedOriginalPreimage_commutator_mem_left
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal})
    (u v : preE7PairAction s p)
    (hu : u ∈ R.rawKernelOmegaFixedOriginalPreimage N) :
    u⁻¹ * v * u * v⁻¹ ∈ N.1 := by
  letI : N.1.Normal := N.2
  apply (QuotientGroup.eq_one_iff _).mp
  simp only [map_mul, map_inv]
  have hcentral : Commute (QuotientGroup.mk' N.1 u)
      (QuotientGroup.mk' N.1 v) :=
    Subgroup.mem_center_iff.mp hu.2.2 (QuotientGroup.mk' N.1 v)
  rw [hcentral.eq]
  group

/-- In particular, two elements of the fixed pullback commute modulo the
original denominator. -/
theorem rawKernelOmegaFixedOriginalPreimage_commutator_mem
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal})
    (u v : preE7PairAction s p)
    (hu : u ∈ R.rawKernelOmegaFixedOriginalPreimage N)
    (hv : v ∈ R.rawKernelOmegaFixedOriginalPreimage N) :
    u⁻¹ * v * u * v⁻¹ ∈ N.1 :=
  R.rawKernelOmegaFixedOriginalPreimage_commutator_mem_left N u v hu

/-- A central normal axis has no coinvariant displacement outside its
denominator axis.  This is the reusable linear form of the calculation
`[D,U] ≤ N`; it applies at either pair frame and after any chosen
identification of its top with a catalogue group. -/
private theorem coinvariantsKer_sharedOriginalAxis_le_ambientAxis
    {X H : Type*} [Group H] {w : ℕ}
    {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w))
    (rho : Representation (ZMod 2) H (Fin w → ZMod 2))
    (e : H ≃* F.top.range)
    (he : ∀ g v, rho g v = F.coordinateTopAction (e g) v)
    (N D : Subgroup U) [N.Normal] [D.Normal]
    (hcentral : ∀ (u : U) (k : F.top.ker),
      (k : U) ∈ D →
        ((k⁻¹ * MulAut.conjNormal u k : F.top.ker) : U) ∈ N) :
    Representation.Coinvariants.ker
        (F.sharedOriginalAxis rho e he D).toRepresentation ≤
      (F.ambientAxis N).comap
        (F.sharedOriginalAxis rho e he D).toSubmodule.subtype := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨g, v⟩, rfl⟩
  obtain ⟨u, hu⟩ := F.top.rangeRestrict_surjective (e g)
  obtain ⟨k, hkD, hkv⟩ := (F.mem_ambientAxis D v.1).1 v.2
  let c : F.top.ker := k⁻¹ * MulAut.conjNormal u k
  have hcN : (c : U) ∈ N := hcentral u k hkD
  change rho g v.1 - v.1 ∈ F.ambientAxis N
  apply (F.mem_ambientAxis N _).2
  refine ⟨c, hcN, ?_⟩
  rw [he, ← hu]
  rw [← hkv, F.coordinateTopAction_bits]
  have hmul := congrArg Multiplicative.toAdd
    (F.bitsHom.map_mul k⁻¹ (MulAut.conjNormal u k))
  have hinv := congrArg Multiplicative.toAdd (F.bitsHom.map_inv k)
  change F.bits c =
    F.bits k⁻¹ + F.bits (MulAut.conjNormal u k) at hmul
  change F.bits k⁻¹ = -F.bits k at hinv
  rw [hmul, hinv, sub_eq_add_neg, add_comm]

/-- Quotienting an invariant state by a subspace containing all intrinsic
displacements costs no more than the state's coinvariant dimension. -/
private theorem nestedQuotient_finrank_le_coinvariants
    {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    {rho : Representation (ZMod 2) G V}
    (A B : Subrepresentation rho) (hAB : A ≤ B)
    (hcoinv : Representation.Coinvariants.ker B.toRepresentation ≤
      A.toSubmodule.comap B.toSubmodule.subtype) :
    Module.finrank (ZMod 2)
        (nestedQuotientRepresentation A B hAB).asModule ≤
      Module.finrank (ZMod 2) B.toRepresentation.Coinvariants := by
  have hA :=
    (A.toSubmodule.comap B.toSubmodule.subtype).finrank_quotient_add_finrank
  have hC :=
    (Representation.Coinvariants.ker
      B.toRepresentation).finrank_quotient_add_finrank
  have hle : Module.finrank (ZMod 2)
      (Representation.Coinvariants.ker B.toRepresentation) ≤
        Module.finrank (ZMod 2)
          (A.toSubmodule.comap B.toSubmodule.subtype) :=
    Submodule.finrank_mono hcoinv
  change Module.finrank (ZMod 2)
      (nestedQuotientRepresentation A B hAB).asModule +
        Module.finrank (ZMod 2)
          (A.toSubmodule.comap B.toSubmodule.subtype) =
      Module.finrank (ZMod 2) B.toSubmodule at hA
  change Module.finrank (ZMod 2) B.toRepresentation.Coinvariants +
      Module.finrank (ZMod 2)
        (Representation.Coinvariants.ker B.toRepresentation) =
      Module.finrank (ZMod 2) B.toSubmodule at hC
  omega

/-- Enlarging a quotient denominator can only decrease its dimension. -/
private theorem finrank_quotient_le_of_le
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (A B : Submodule (ZMod 2) V) (hAB : A ≤ B) :
    Module.finrank (ZMod 2) (V ⧸ B) ≤
      Module.finrank (ZMod 2) (V ⧸ A) := by
  have hA := A.finrank_quotient_add_finrank
  have hB := B.finrank_quotient_add_finrank
  have hle := Submodule.finrank_mono hAB
  omega

/-! ## The three literal axes of the fixed lift -/

/-- The second-kernel coordinate state contributed by the fixed omega
lift.  This is `K` in the coupled three-head inequality. -/
def fixedOmegaInnerNaturalAxis
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) D.top (Fin t)) :=
  R.secondFrame.sharedOriginalAxis
    (permutationFunctionRepresentation (ZMod 2) D.top (Fin t))
    R.topEquiv R.module_action_eq
    (R.rawKernelOmegaFixedIntermediatePreimage N)

/-- The fixed inner axis before transporting the second-frame top to the
literal catalogue top. -/
def fixedOmegaInnerCoordinateAxis
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Subrepresentation R.secondFrame.coordinateTopAction :=
  R.secondFrame.sharedOriginalAxis
    R.secondFrame.coordinateTopAction (MulEquiv.refl _) (fun _ _ ↦ rfl)
    (R.rawKernelOmegaFixedIntermediatePreimage N)

/-- The first-kernel coordinate state contributed by the fixed omega lift,
before separating its pair-sum and pair-constant coordinates. -/
def fixedOmegaOuterAxis
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Subrepresentation
      (permutationFunctionRepresentation (ZMod 2)
        R.frame.top.range (Fin s)) :=
  R.frame.sharedOriginalAxis
    (permutationFunctionRepresentation (ZMod 2)
      R.frame.top.range (Fin s))
    (MulEquiv.refl R.frame.top.range) (fun _ _ ↦ rfl)
    (R.rawKernelOmegaFixedOriginalPreimage N)

/-- Pair-sum image `W` of the fixed first-kernel state. -/
def fixedOmegaPairSumPullbackAxis
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Subrepresentation R.secondFrame.pulledBackCoordinateTopAction :=
  intertwinerImage
    (permutationFunctionRepresentation (ZMod 2)
      R.frame.top.range (Fin s))
    R.secondFrame.pulledBackCoordinateTopAction
    R.secondFrame.pairSumIntertwiner (R.fixedOmegaOuterAxis N)

/-- Pair-constant preimage `L` of the fixed first-kernel state. -/
def fixedOmegaConstantPullbackAxis
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Subrepresentation R.secondFrame.pulledBackCoordinateTopAction :=
  intertwinerPreimage
    R.secondFrame.pulledBackCoordinateTopAction
    (permutationFunctionRepresentation (ZMod 2)
      R.frame.top.range (Fin s))
    R.secondFrame.pairConstantIntertwiner (R.fixedOmegaOuterAxis N)

/-- Transport the fixed pair-sum state to the literal bottom top. -/
def fixedOmegaPairSumAxis
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) D.top (Fin t)) :=
  R.transportInnerNaturalAxis
    (R.secondFrame.descendPulledBackSubrepresentation
      (R.fixedOmegaPairSumPullbackAxis N))

/-- Transport the fixed pair-constant state to the literal bottom top. -/
def fixedOmegaConstantAxis
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) D.top (Fin t)) :=
  R.transportInnerNaturalAxis
    (R.secondFrame.descendPulledBackSubrepresentation
      (R.fixedOmegaConstantPullbackAxis N))

theorem fixedOmegaInnerNaturalAxis_toSubmodule
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (R.fixedOmegaInnerNaturalAxis N).toSubmodule =
      R.secondFrame.ambientAxis
        ((R.rawKernelOmegaFixedOriginalPreimage N).map
          R.frame.top.rangeRestrict) :=
  congrArg R.secondFrame.ambientAxis
    (R.rawKernelOmegaFixedIntermediatePreimage_eq_map N)

theorem fixedOmegaInnerCoordinateAxis_le_kernelTop
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    R.fixedOmegaInnerCoordinateAxis N ≤
      R.secondFrame.kernelTopPermutationSubrepresentation :=
  R.secondFrame.ambientAxis_le_kernelSpace
    (R.rawKernelOmegaFixedIntermediatePreimage N)

theorem fixedOmegaPairSumAxis_toSubmodule
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (R.fixedOmegaPairSumAxis N).toSubmodule =
      (R.frame.ambientAxis
          (R.rawKernelOmegaFixedOriginalPreimage N)).map
        R.secondFrame.pairSum :=
  rfl

theorem fixedOmegaConstantAxis_toSubmodule
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (R.fixedOmegaConstantAxis N).toSubmodule =
      (R.frame.ambientAxis
          (R.rawKernelOmegaFixedOriginalPreimage N)).comap
        R.secondFrame.pairConstant :=
  rfl

theorem moduleAxis_le_fixedOmegaInnerNaturalAxis
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    R.moduleAxis N ≤ R.fixedOmegaInnerNaturalAxis N := by
  intro v hv
  change v ∈ R.secondFrame.ambientAxis
    (R.rawKernelOmegaFixedIntermediatePreimage N)
  change v ∈ R.secondFrame.ambientAxis (R.outerTopNormal N.1) at hv
  obtain ⟨k, hk, rfl⟩ := (R.secondFrame.mem_ambientAxis _ v).1 hv
  exact (R.secondFrame.mem_ambientAxis _ _).2
    ⟨k, R.outerTopNormal_le_rawKernelOmegaFixedIntermediatePreimage N hk,
      rfl⟩

theorem innerNormalCoordinateAxis_le_fixedOmegaInnerCoordinateAxis
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    R.innerNormalCoordinateAxis N ≤ R.fixedOmegaInnerCoordinateAxis N := by
  intro v hv
  change v ∈ R.secondFrame.ambientAxis
    (R.rawKernelOmegaFixedIntermediatePreimage N)
  change v ∈ R.secondFrame.ambientAxis (R.outerTopNormal N.1) at hv
  obtain ⟨k, hk, rfl⟩ := (R.secondFrame.mem_ambientAxis _ v).1 hv
  exact (R.secondFrame.mem_ambientAxis _ _).2
    ⟨k, R.outerTopNormal_le_rawKernelOmegaFixedIntermediatePreimage N hk,
      rfl⟩

theorem outerNormalAxis_le_fixedOmegaOuterAxis
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    R.frame.normalTopPermutationSubrepresentation N.1 ≤
      R.fixedOmegaOuterAxis N := by
  intro v hv
  change v ∈ R.frame.ambientAxis
    (R.rawKernelOmegaFixedOriginalPreimage N)
  rw [R.frame.normalSpace_map_subtype_eq_ambientAxis N.1] at hv
  obtain ⟨k, hk, rfl⟩ := (R.frame.mem_ambientAxis N.1 v).1 hv
  exact (R.frame.mem_ambientAxis _ _).2
    ⟨k, R.originalNormal_le_rawKernelOmegaFixedOriginalPreimage N hk, rfl⟩

theorem outerNormalPairSum_le_fixedOmegaPairSum
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    R.outerNormalPairSumPullbackAxis N ≤
      R.fixedOmegaPairSumPullbackAxis N :=
  intertwinerImage_mono _ _ _
    (R.outerNormalAxis_le_fixedOmegaOuterAxis N)

theorem outerNormalPairSumAxis_le_fixedOmegaPairSumAxis
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    R.outerNormalPairSumAxis N ≤ R.fixedOmegaPairSumAxis N :=
  R.outerNormalPairSum_le_fixedOmegaPairSum N

theorem outerNormalConstant_le_fixedOmegaConstant
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    R.outerNormalConstantAxis N ≤ R.fixedOmegaConstantAxis N := by
  intro v hv
  change v ∈
    (R.frame.ambientAxis
      (R.rawKernelOmegaFixedOriginalPreimage N)).comap
        R.secondFrame.pairConstant
  change R.secondFrame.pairConstant v ∈ R.frame.ambientAxis N.1 at hv
  obtain ⟨k, hk, hkv⟩ := (R.frame.mem_ambientAxis N.1 _).1 hv
  exact (R.frame.mem_ambientAxis _ _).2
    ⟨k, R.originalNormal_le_rawKernelOmegaFixedOriginalPreimage N hk, hkv⟩

/-- The fixed inner layer after removing the original-normal axis. -/
abbrev fixedOmegaInnerQuotientRepresentation
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :=
  nestedQuotientRepresentation
    (R.moduleAxis N) (R.fixedOmegaInnerNaturalAxis N)
    (R.moduleAxis_le_fixedOmegaInnerNaturalAxis N)

/-- The image of the fixed inner coordinate quotient in the actual second
section module. -/
abbrev fixedOmegaInnerSectionImage
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :=
  intertwinerImage
    R.secondFrame.kernelTopPermutationSubrepresentation.toRepresentation
    (R.secondFrame.sectionTopRepresentation (R.outerTopNormal N.1))
    (R.secondFrame.sectionTopIntertwiner (R.outerTopNormal N.1))
    (nestedSubrepresentation (R.fixedOmegaInnerCoordinateAxis N)
      R.secondFrame.kernelTopPermutationSubrepresentation
      (R.fixedOmegaInnerCoordinateAxis_le_kernelTop N))

/-- The coordinate section image is the actual section image of the fixed
intermediate subgroup. -/
theorem fixedOmegaInnerSectionImage_toSubmodule
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (R.fixedOmegaInnerSectionImage N).toSubmodule =
      (R.fixedOmegaInnerSubrepresentation N).toSubmodule := by
  letI : (R.outerTopNormal N.1).Normal := R.outerTopNormal_normal N.1
  let E := R.innerSectionModuleChart N
  let L := (R.rawKernelOmegaFixedTopImage N).subgroupOf
    (R.innerQuotientMap N).ker
  have hker : (E.kernelCoordinates
      (R.innerQuotientMap N) (R.innerSectionModule N)).ker ≤ L := by
    intro x hx
    have hx1 : x = 1 := by
      apply E.equiv.symm.injective
      exact (MonoidHom.mem_ker.mp hx).trans
        (map_one E.equiv.symm).symm
    subst x
    exact Subgroup.one_mem _
  ext v
  constructor
  · rintro ⟨b, hb, rfl⟩
    change b.1 ∈ (R.fixedOmegaInnerCoordinateAxis N).toSubmodule at hb
    change b.1 ∈ R.secondFrame.ambientAxis
      (R.rawKernelOmegaFixedIntermediatePreimage N) at hb
    obtain ⟨k, hk, hkb⟩ :=
      (R.secondFrame.mem_ambientAxis _ b.1).1 hb
    have hbEq : (R.secondFrame.kernelSpaceHom k).toAdd = b := by
      apply Subtype.ext
      exact hkb
    rw [← hbEq]
    change ((E.kernelCoordinates
      (R.innerQuotientMap N) (R.innerSectionModule N)
      (E.equiv (Multiplicative.ofAdd
        ((R.secondFrame.normalSpace (R.outerTopNormal N.1)).mkQ
          (R.secondFrame.kernelSpaceHom k).toAdd)))).toAdd) ∈
      E.normalSpace (R.innerQuotientMap N)
        (R.innerSectionModule N) L
    apply (sectionSubgroupImage_mem_iff
      (E.kernelCoordinates (R.innerQuotientMap N)
        (R.innerSectionModule N)) L hker _).2
    change (E.equiv (Multiplicative.ofAdd
      ((R.secondFrame.normalSpace (R.outerTopNormal N.1)).mkQ
        (R.secondFrame.kernelSpaceHom k).toAdd)) :
          R.frame.top.range ⨸ R.outerTopNormal N.1) ∈
      R.rawKernelOmegaFixedTopImage N
    have he := R.secondFrame.literalSectionModuleChart_equiv_mk
      R.topEquiv (R.outerTopNormal N.1) k
    rw [show E = R.secondFrame.literalSectionModuleChart
      R.topEquiv (R.outerTopNormal N.1) from rfl]
    rw [he]
    exact hk
  · intro hv
    change v ∈ E.normalSpace (R.innerQuotientMap N)
      (R.innerSectionModule N) L at hv
    let y : (R.innerQuotientMap N).ker :=
      E.equiv (Multiplicative.ofAdd v)
    have hcoord : (E.kernelCoordinates
        (R.innerQuotientMap N) (R.innerSectionModule N) y).toAdd = v := by
      change (E.equiv.symm (E.equiv (Multiplicative.ofAdd v))).toAdd = v
      rw [E.equiv.symm_apply_apply]
      rfl
    have hy : y ∈ L := by
      apply (sectionSubgroupImage_mem_iff
        (E.kernelCoordinates (R.innerQuotientMap N)
          (R.innerSectionModule N)) L hker y).1
      rwa [hcoord]
    obtain ⟨x, hx⟩ :=
      (R.secondFrame.normalSpace (R.outerTopNormal N.1)).mkQ_surjective v
    obtain ⟨k, hk⟩ := R.secondFrame.kernelSpaceHom_bijective.2
      (Multiplicative.ofAdd x)
    have hxk : (R.secondFrame.kernelSpaceHom k).toAdd = x :=
      congrArg Multiplicative.toAdd hk
    have hyval :
        (y : R.frame.top.range ⨸ R.outerTopNormal N.1) =
          QuotientGroup.mk' (R.outerTopNormal N.1)
            (k : R.frame.top.range) := by
      change ((E.equiv (Multiplicative.ofAdd v) :
        (R.innerQuotientMap N).ker) :
          R.frame.top.range ⨸ R.outerTopNormal N.1) = _
      rw [← hx, ← hxk]
      have he := R.secondFrame.literalSectionModuleChart_equiv_mk
        R.topEquiv (R.outerTopNormal N.1) k
      simpa only [E, innerSectionModuleChart, innerSectionModule,
        innerQuotientMap] using he
    have hkFixed : (k : R.frame.top.range) ∈
        R.rawKernelOmegaFixedIntermediatePreimage N := by
      change QuotientGroup.mk' (R.outerTopNormal N.1)
        (k : R.frame.top.range) ∈ R.rawKernelOmegaFixedTopImage N
      rw [← hyval]
      exact hy
    let b : R.secondFrame.kernelTopPermutationSubrepresentation.toSubmodule :=
      (R.secondFrame.kernelSpaceHom k).toAdd
    have hb : b.1 ∈ (R.fixedOmegaInnerCoordinateAxis N).toSubmodule := by
      change R.secondFrame.bits k ∈
        R.secondFrame.ambientAxis
          (R.rawKernelOmegaFixedIntermediatePreimage N)
      exact (R.secondFrame.bits_mem_ambientAxis _ k).2 hkFixed
    refine ⟨b, hb, ?_⟩
    change (R.secondFrame.normalSpace (R.outerTopNormal N.1)).mkQ b = v
    rw [show (b : R.secondFrame.kernelSpace) = x from hxk, hx]

/-- Transporting the fixed inner quotient to the physical second top leaves
its underlying quotient unchanged. -/
def fixedOmegaInnerQuotientCoordinateEquiv
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    ((R.fixedOmegaInnerQuotientRepresentation N).comp
      R.topEquiv.symm.toMonoidHom).Equiv
      (nestedQuotientRepresentation
        (R.innerNormalCoordinateAxis N)
        (R.fixedOmegaInnerCoordinateAxis N)
        (R.innerNormalCoordinateAxis_le_fixedOmegaInnerCoordinateAxis N)) :=
  Representation.Equiv.mk (LinearEquiv.refl _ _) (by
    intro g
    apply LinearMap.ext
    intro x
    obtain ⟨b, rfl⟩ :=
      (nestedSubrepresentation
        (R.moduleAxis N) (R.fixedOmegaInnerNaturalAxis N)
        (R.moduleAxis_le_fixedOmegaInnerNaturalAxis N)).toSubmodule.
          mkQ_surjective x
    apply congrArg
      (nestedSubrepresentation
        (R.innerNormalCoordinateAxis N)
        (R.fixedOmegaInnerCoordinateAxis N)
        (R.innerNormalCoordinateAxis_le_fixedOmegaInnerCoordinateAxis N)).
          toSubmodule.mkQ
    apply Subtype.ext
    rw [R.module_action_eq, R.topEquiv.apply_symm_apply])

/-- The fixed inner quotient is the exact fixed coordinate image in the
actual second-frame section. -/
noncomputable def fixedOmegaInnerQuotientSectionImageEquiv
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    ((R.fixedOmegaInnerQuotientRepresentation N).comp
      R.topEquiv.symm.toMonoidHom).Equiv
      (R.fixedOmegaInnerSectionImage N).toRepresentation := by
  let hAB : R.secondFrame.normalTopPermutationSubrepresentation
      (R.outerTopNormal N.1) ≤ R.fixedOmegaInnerCoordinateAxis N := by
    rw [← R.innerNormalCoordinateAxis_eq_normalTopPermutation N]
    exact R.innerNormalCoordinateAxis_le_fixedOmegaInnerCoordinateAxis N
  let eImage := R.secondFrame.sectionTopNestedQuotientImageEquiv
    (R.outerTopNormal N.1) (R.fixedOmegaInnerCoordinateAxis N) hAB
      (R.fixedOmegaInnerCoordinateAxis_le_kernelTop N)
  rw [← R.innerNormalCoordinateAxis_eq_normalTopPermutation N] at eImage
  exact (R.fixedOmegaInnerQuotientCoordinateEquiv N).trans eImage

/-- The fixed outer layer after removing the original-normal axis. -/
abbrev fixedOmegaOuterQuotientRepresentation
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :=
  nestedQuotientRepresentation
    (R.frame.normalTopPermutationSubrepresentation N.1)
    (R.fixedOmegaOuterAxis N)
    (R.outerNormalAxis_le_fixedOmegaOuterAxis N)

/-- The literal fixed pair-sum quotient over the catalogue top. -/
abbrev fixedOmegaPairSumQuotientRepresentation
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :=
  nestedQuotientRepresentation
    (R.outerNormalPairSumAxis N) (R.fixedOmegaPairSumAxis N)
    (R.outerNormalPairSumAxis_le_fixedOmegaPairSumAxis N)

/-- The literal fixed pair-constant quotient over the catalogue top. -/
abbrev fixedOmegaConstantQuotientRepresentation
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :=
  nestedQuotientRepresentation
    (R.outerNormalConstantAxis N) (R.fixedOmegaConstantAxis N)
    (R.outerNormalConstant_le_fixedOmegaConstant N)

/-- Pair-sum on the fixed outer quotient. -/
noncomputable def fixedOmegaOuterPairSumMap
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (R.fixedOmegaOuterQuotientRepresentation N).IntertwiningMap
      (nestedQuotientRepresentation
        (R.outerNormalPairSumPullbackAxis N)
        (R.fixedOmegaPairSumPullbackAxis N)
        (R.outerNormalPairSum_le_fixedOmegaPairSum N)) :=
  nestedQuotientMap
    (permutationFunctionRepresentation (ZMod 2)
      R.frame.top.range (Fin s))
    R.secondFrame.pulledBackCoordinateTopAction
    R.secondFrame.pairSumIntertwiner
    (R.frame.normalTopPermutationSubrepresentation N.1)
    (R.fixedOmegaOuterAxis N)
    (R.outerNormalAxis_le_fixedOmegaOuterAxis N)

theorem fixedOmegaOuterPairSumMap_surjective
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Function.Surjective (R.fixedOmegaOuterPairSumMap N) :=
  nestedQuotientMap_surjective _ _ _ _ _ _

/-- The kernel of fixed outer pair-sum is exactly the fixed constant
quotient. -/
noncomputable def fixedOmegaOuterPairSumKernelEquiv
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (nestedQuotientRepresentation
      (R.outerNormalConstantPullbackAxis N)
      (R.fixedOmegaConstantPullbackAxis N)
      (intertwinerPreimage_mono _ _ _
        (R.outerNormalAxis_le_fixedOmegaOuterAxis N))).Equiv
      (R.fixedOmegaOuterPairSumMap N).ker.toRepresentation :=
  nestedQuotientMapKernelEquiv
    R.secondFrame.pulledBackCoordinateTopAction
    (permutationFunctionRepresentation (ZMod 2)
      R.frame.top.range (Fin s))
    R.secondFrame.pulledBackCoordinateTopAction
    R.secondFrame.pairConstantIntertwiner
    R.secondFrame.pairSumIntertwiner
    R.secondFrame.pairConstantIntertwiner_injective
    R.secondFrame.pairConstant_pairSum_exact_linear
    (R.frame.normalTopPermutationSubrepresentation N.1)
    (R.fixedOmegaOuterAxis N)
    (R.outerNormalAxis_le_fixedOmegaOuterAxis N)

/-- Transport the fixed pair-sum quotient from the first physical top to
the literal catalogue top. -/
noncomputable def fixedOmegaPairSumPullbackQuotientEquiv
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (nestedQuotientRepresentation
      (R.outerNormalPairSumPullbackAxis N)
      (R.fixedOmegaPairSumPullbackAxis N)
      (R.outerNormalPairSum_le_fixedOmegaPairSum N)).Equiv
      ((R.fixedOmegaPairSumQuotientRepresentation N).comp
        R.outerTopToLiteral) :=
  R.outerPullbackNestedQuotientEquiv _ _ _

/-- Transport the fixed pair-constant quotient to the literal catalogue
top. -/
noncomputable def fixedOmegaConstantPullbackQuotientEquiv
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (nestedQuotientRepresentation
      (R.outerNormalConstantPullbackAxis N)
      (R.fixedOmegaConstantPullbackAxis N)
      (intertwinerPreimage_mono _ _ _
        (R.outerNormalAxis_le_fixedOmegaOuterAxis N))).Equiv
      ((R.fixedOmegaConstantQuotientRepresentation N).comp
        R.outerTopToLiteral) :=
  R.outerPullbackNestedQuotientEquiv _ _ _

/-- Intrinsic displacements of the fixed inner axis already lie in the
literal normal denominator. -/
theorem fixedOmegaInner_coinvariantsKer_le_moduleAxis
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Representation.Coinvariants.ker
        (R.fixedOmegaInnerNaturalAxis N).toRepresentation ≤
      (R.moduleAxis N).toSubmodule.comap
        (R.fixedOmegaInnerNaturalAxis N).toSubmodule.subtype := by
  change Representation.Coinvariants.ker
      (R.secondFrame.sharedOriginalAxis
        (permutationFunctionRepresentation (ZMod 2) D.top (Fin t))
        R.topEquiv R.module_action_eq
        (R.rawKernelOmegaFixedIntermediatePreimage N)).toRepresentation ≤
    (R.secondFrame.ambientAxis (R.outerTopNormal N.1)).comap _
  rw [R.rawKernelOmegaFixedIntermediatePreimage_eq_map N]
  apply coinvariantsKer_sharedOriginalAxis_le_ambientAxis
    R.secondFrame
    (permutationFunctionRepresentation (ZMod 2) D.top (Fin t))
    R.topEquiv R.module_action_eq
    (R.outerTopNormal N.1)
    ((R.rawKernelOmegaFixedOriginalPreimage N).map
      R.frame.top.rangeRestrict)
  intro u k hk
  obtain ⟨a, ha⟩ := R.frame.top.rangeRestrict_surjective u
  obtain ⟨v, hvD, hvk⟩ := hk
  refine ⟨v⁻¹ * a * v * a⁻¹,
    R.rawKernelOmegaFixedOriginalPreimage_commutator_mem_left N v a hvD,
    ?_⟩
  apply Subtype.ext
  simp only [map_mul, map_inv, ha, hvk]
  rfl

/-- Intrinsic displacements of the fixed outer axis lie in the first-frame
normal denominator. -/
theorem fixedOmegaOuter_coinvariantsKer_le_normalAxis
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Representation.Coinvariants.ker
        (R.fixedOmegaOuterAxis N).toRepresentation ≤
      (R.frame.ambientAxis N.1).comap
        (R.fixedOmegaOuterAxis N).toSubmodule.subtype := by
  exact coinvariantsKer_sharedOriginalAxis_le_ambientAxis
    R.frame
    (permutationFunctionRepresentation (ZMod 2)
      R.frame.top.range (Fin s))
    (MulEquiv.refl R.frame.top.range) (fun _ _ ↦ rfl)
    N.1 (R.rawKernelOmegaFixedOriginalPreimage N)
    (fun u k hk ↦
      R.rawKernelOmegaFixedOriginalPreimage_commutator_mem_left
        N k.1 u hk)

/-- Pair-sum carries every fixed-outer displacement into the corresponding
normal pair-sum axis. -/
theorem fixedOmegaPairSum_coinvariantsKer_le_normalAxis
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Representation.Coinvariants.ker
        (R.fixedOmegaPairSumAxis N).toRepresentation ≤
      (R.outerNormalPairSumAxis N).toSubmodule.comap
        (R.fixedOmegaPairSumAxis N).toSubmodule.subtype := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨g, w⟩, rfl⟩
  change permutationFunctionRepresentation (ZMod 2) D.top (Fin t)
      g w.1 - w.1 ∈
    (R.frame.ambientAxis N.1).map R.secondFrame.pairSum
  change w.1 ∈
    (R.frame.ambientAxis
      (R.rawKernelOmegaFixedOriginalPreimage N)).map
        R.secondFrame.pairSum at w.2
  obtain ⟨b, hb, hbw⟩ := w.2
  obtain ⟨u, hu⟩ := R.secondFrame.top.rangeRestrict_surjective
    (R.topEquiv g)
  let bD : (R.fixedOmegaOuterAxis N).toSubmodule := ⟨b, hb⟩
  have hbnormal :
      (R.fixedOmegaOuterAxis N).toRepresentation u bD - bD ∈
        (R.frame.ambientAxis N.1).comap
          (R.fixedOmegaOuterAxis N).toSubmodule.subtype :=
    R.fixedOmegaOuter_coinvariantsKer_le_normalAxis N
      (Representation.Coinvariants.sub_mem_ker
        (ρ := (R.fixedOmegaOuterAxis N).toRepresentation) u bD)
  refine ⟨((R.fixedOmegaOuterAxis N).toRepresentation u bD - bD).1,
    hbnormal, ?_⟩
  rw [map_sub]
  change R.secondFrame.pairSum
      ((R.fixedOmegaOuterAxis N).toRepresentation u bD).1 -
        R.secondFrame.pairSum b = _
  rw [show R.secondFrame.pairSum
      ((R.fixedOmegaOuterAxis N).toRepresentation u bD).1 =
        R.secondFrame.pulledBackCoordinateTopAction u
          (R.secondFrame.pairSum b) from
    congrArg Subtype.val
      (Representation.IntertwiningMap.isIntertwining _ _
        R.secondFrame.pairSumIntertwiner u bD)]
  change R.secondFrame.coordinateTopAction
      (R.secondFrame.top.rangeRestrict u) (R.secondFrame.pairSum b) -
        R.secondFrame.pairSum b = _
  rw [hu, ← R.module_action_eq, hbw]

/-- Pair-constant pulls every displacement of the fixed constant axis back
to the normal constant axis. -/
theorem fixedOmegaConstant_coinvariantsKer_le_normalAxis
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Representation.Coinvariants.ker
        (R.fixedOmegaConstantAxis N).toRepresentation ≤
      (R.outerNormalConstantAxis N).toSubmodule.comap
        (R.fixedOmegaConstantAxis N).toSubmodule.subtype := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨g, a⟩, rfl⟩
  change R.secondFrame.pairConstant
      (permutationFunctionRepresentation (ZMod 2) D.top (Fin t)
        g a.1 - a.1) ∈ R.frame.ambientAxis N.1
  obtain ⟨u, hu⟩ := R.secondFrame.top.rangeRestrict_surjective
    (R.topEquiv g)
  let bD : (R.fixedOmegaOuterAxis N).toSubmodule :=
    ⟨R.secondFrame.pairConstant a.1, a.2⟩
  have hbnormal :
      (R.fixedOmegaOuterAxis N).toRepresentation u bD - bD ∈
        (R.frame.ambientAxis N.1).comap
          (R.fixedOmegaOuterAxis N).toSubmodule.subtype :=
    R.fixedOmegaOuter_coinvariantsKer_le_normalAxis N
      (Representation.Coinvariants.sub_mem_ker
        (ρ := (R.fixedOmegaOuterAxis N).toRepresentation) u bD)
  change ((R.fixedOmegaOuterAxis N).toRepresentation u bD - bD).1 ∈
    R.frame.ambientAxis N.1 at hbnormal
  rw [R.module_action_eq, ← hu]
  rw [map_sub]
  rw [show R.secondFrame.pairConstant
      (R.secondFrame.pulledBackCoordinateTopAction u a.1) =
        ((R.fixedOmegaOuterAxis N).toRepresentation u bD).1 from
    congrArg Subtype.val
      (Representation.IntertwiningMap.isIntertwining _ _
        R.secondFrame.pairConstantIntertwiner u a.1)]
  change ((R.fixedOmegaOuterAxis N).toRepresentation u bD).1 - bD.1 ∈ _
  exact hbnormal

/-- The fixed outer quotient splits exactly into its pair-constant and
pair-sum quotients. -/
theorem fixedOmegaOuterQuotient_finrank_eq_constant_add_pairSum
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Module.finrank (ZMod 2)
        (R.fixedOmegaOuterQuotientRepresentation N).asModule =
      Module.finrank (ZMod 2)
          (R.fixedOmegaConstantQuotientRepresentation N).asModule +
        Module.finrank (ZMod 2)
          (R.fixedOmegaPairSumQuotientRepresentation N).asModule := by
  let q := R.fixedOmegaOuterPairSumMap N
  have hdim := q.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr
    (R.fixedOmegaOuterPairSumMap_surjective N), finrank_top] at hdim
  have hker :=
    (R.fixedOmegaOuterPairSumKernelEquiv N).toLinearEquiv.finrank_eq
  have hsum :=
    (R.fixedOmegaPairSumPullbackQuotientEquiv N).toLinearEquiv.finrank_eq
  have hconstant :=
    (R.fixedOmegaConstantPullbackQuotientEquiv N).toLinearEquiv.finrank_eq
  change Module.finrank (ZMod 2)
      (nestedQuotientRepresentation
        (R.outerNormalPairSumPullbackAxis N)
        (R.fixedOmegaPairSumPullbackAxis N)
        (R.outerNormalPairSum_le_fixedOmegaPairSum N)).asModule +
      Module.finrank (ZMod 2) q.ker =
    Module.finrank (ZMod 2)
      (R.fixedOmegaOuterQuotientRepresentation N).asModule at hdim
  change Module.finrank (ZMod 2)
      (nestedQuotientRepresentation
        (R.outerNormalConstantPullbackAxis N)
        (R.fixedOmegaConstantPullbackAxis N)
        (intertwinerPreimage_mono _ _ _
          (R.outerNormalAxis_le_fixedOmegaOuterAxis N))).asModule =
    Module.finrank (ZMod 2) q.ker at hker
  change Module.finrank (ZMod 2)
      (nestedQuotientRepresentation
        (R.outerNormalPairSumPullbackAxis N)
        (R.fixedOmegaPairSumPullbackAxis N)
        (R.outerNormalPairSum_le_fixedOmegaPairSum N)).asModule =
    Module.finrank (ZMod 2)
      (R.fixedOmegaPairSumQuotientRepresentation N).asModule at hsum
  change Module.finrank (ZMod 2)
      (nestedQuotientRepresentation
        (R.outerNormalConstantPullbackAxis N)
        (R.fixedOmegaConstantPullbackAxis N)
        (intertwinerPreimage_mono _ _ _
          (R.outerNormalAxis_le_fixedOmegaOuterAxis N))).asModule =
    Module.finrank (ZMod 2)
      (R.fixedOmegaConstantQuotientRepresentation N).asModule at hconstant
  omega

theorem fixedOmegaInnerQuotient_finrank_le_coinvariants
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Module.finrank (ZMod 2)
        (R.fixedOmegaInnerQuotientRepresentation N).asModule ≤
      Module.finrank (ZMod 2)
        (R.fixedOmegaInnerNaturalAxis N).toRepresentation.Coinvariants :=
  nestedQuotient_finrank_le_coinvariants
    (R.moduleAxis N) (R.fixedOmegaInnerNaturalAxis N)
    (R.moduleAxis_le_fixedOmegaInnerNaturalAxis N)
    (R.fixedOmegaInner_coinvariantsKer_le_moduleAxis N)

theorem fixedOmegaPairSumQuotient_finrank_le_coinvariants
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Module.finrank (ZMod 2)
        (R.fixedOmegaPairSumQuotientRepresentation N).asModule ≤
      Module.finrank (ZMod 2)
        (R.fixedOmegaPairSumAxis N).toRepresentation.Coinvariants :=
  nestedQuotient_finrank_le_coinvariants
    (R.outerNormalPairSumAxis N) (R.fixedOmegaPairSumAxis N)
    (R.outerNormalPairSumAxis_le_fixedOmegaPairSumAxis N)
    (R.fixedOmegaPairSum_coinvariantsKer_le_normalAxis N)

/-- The fixed-lift product lies in the literal original-normal constant
denominator.  This is the formal `[B,D] = KW ≤ L ∩ N` step. -/
theorem fixedOmega_productSpan_le_normalConstant
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    binaryCoordinateProductSpan
        (R.fixedOmegaInnerNaturalAxis N).toSubmodule
        (R.fixedOmegaPairSumAxis N).toSubmodule ≤
      (R.outerNormalConstantAxis N).toSubmodule := by
  rw [R.fixedOmegaInnerNaturalAxis_toSubmodule N,
    R.fixedOmegaPairSumAxis_toSubmodule N]
  change binaryCoordinateProductSpan
      (R.secondFrame.ambientAxis
        ((R.rawKernelOmegaFixedOriginalPreimage N).map
          R.frame.top.rangeRestrict))
      ((R.frame.ambientAxis
        (R.rawKernelOmegaFixedOriginalPreimage N)).map
          R.secondFrame.pairSum) ≤
    (R.frame.ambientAxis N.1).comap R.secondFrame.pairConstant
  exact R.frame.nestedPair_productSpan_le_normalConstantPreimage
    R.secondFrame N.1 (R.rawKernelOmegaFixedOriginalPreimage N)
    (R.originalNormal_le_rawKernelOmegaFixedOriginalPreimage N)
    (by
      intro u hu k hk
      exact R.rawKernelOmegaFixedOriginalPreimage_commutator_mem
        N k.1 u hk hu)

theorem fixedOmega_productSpan_le_constant
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    binaryCoordinateProductSpan
        (R.fixedOmegaInnerNaturalAxis N).toSubmodule
        (R.fixedOmegaPairSumAxis N).toSubmodule ≤
      (R.fixedOmegaConstantAxis N).toSubmodule :=
  (R.fixedOmega_productSpan_le_normalConstant N).trans
    (R.outerNormalConstant_le_fixedOmegaConstant N)

/-- The coupled product/displacement denominator is contained in the
literal normal constant denominator. -/
theorem fixedOmegaCoupledDenominator_le_normalConstant
    {J : Type*} (generators : J → D.top)
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    binaryCoupledDenominator
        (permutationFunctionRepresentation (ZMod 2) D.top (Fin t))
        generators (R.fixedOmegaConstantAxis N)
        (binaryCoordinateProductSpan
          (R.fixedOmegaInnerNaturalAxis N).toSubmodule
          (R.fixedOmegaPairSumAxis N).toSubmodule)
        (R.fixedOmega_productSpan_le_constant N) ≤
      (R.outerNormalConstantAxis N).toSubmodule.comap
        (R.fixedOmegaConstantAxis N).toSubmodule.subtype := by
  apply sup_le
  · intro z hz
    exact R.fixedOmega_productSpan_le_normalConstant N hz
  · exact (representationGeneratorDisplacementSpan_le_coinvariantsKer
      (permutationFunctionRepresentation (ZMod 2) D.top (Fin t))
      generators (R.fixedOmegaConstantAxis N)).trans
        (R.fixedOmegaConstant_coinvariantsKer_le_normalAxis N)

/-- Consequently the normal constant quotient is no larger than the third
coupled catalogue term. -/
theorem fixedOmegaConstantQuotient_finrank_le_coupled
    {J : Type*} (generators : J → D.top)
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Module.finrank (ZMod 2)
        (R.fixedOmegaConstantQuotientRepresentation N).asModule ≤
      Module.finrank (ZMod 2)
        ((R.fixedOmegaConstantAxis N).toSubmodule ⫽
          binaryCoupledDenominator
            (permutationFunctionRepresentation (ZMod 2) D.top (Fin t))
            generators (R.fixedOmegaConstantAxis N)
            (binaryCoordinateProductSpan
              (R.fixedOmegaInnerNaturalAxis N).toSubmodule
              (R.fixedOmegaPairSumAxis N).toSubmodule)
            (R.fixedOmega_productSpan_le_constant N)) := by
  exact finrank_quotient_le_of_le
    (binaryCoupledDenominator
      (permutationFunctionRepresentation (ZMod 2) D.top (Fin t))
      generators (R.fixedOmegaConstantAxis N)
      (binaryCoordinateProductSpan
        (R.fixedOmegaInnerNaturalAxis N).toSubmodule
        (R.fixedOmegaPairSumAxis N).toSubmodule)
      (R.fixedOmega_productSpan_le_constant N))
    ((R.outerNormalConstantAxis N).toSubmodule.comap
      (R.fixedOmegaConstantAxis N).toSubmodule.subtype)
    (R.fixedOmegaCoupledDenominator_le_normalConstant generators N)

end DegreeTwoPairTopTowerRealization
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
