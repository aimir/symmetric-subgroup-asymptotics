import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeNineSocleGenerators
import SymmetricSubgroupAsymptotics.PrimeSectionalCharacterRank
import SymmetricSubgroupAsymptotics.PermutationSectionNormalGenerators

/-!
# The whole linear core in the degree-nine affine frame

The correct reusable split uses the whole kernel of the action on the
original blocks.  Its preimage in the original action contains the literal
translation intersection, and the quotient is the literal transitive block
top.  On a retained normal axis this gives both an injective top-section map
for every core-disjoint normal subgroup and the sharp prime-sectional rank
of the top.

No finite subgroup catalogue of `GL(2,3)` occurs here.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

private abbrev LiteralNormalAxis (G : Type) [Group G] :=
  {N : Subgroup G // N.Normal}

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)

variable [Nontrivial block.Fibre]

/-! ## The local degree-nine parameters -/

/-- A degree-nine elementary translation module has characteristic three
and dimension two. -/
theorem degreeNine_translationParameters
    (hr : Nat.card block.Fibre = 9) :
    P.p = 3 ∧ (chart block P).d = 2 := by
  let C := chart block P
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v))
    C.equiv.symm.injective
  have hdegree : 9 = P.p ^ C.d := by
    rw [← hr]
    simpa [PrimitiveAffineProfile.ElementaryChart.d] using
      P.degree_eq_prime_pow_finrank C.equiv (origin block)
  exact prime_pow_positive_injective (d := C.d) (e := 2)
    P.p_prime (by norm_num : Nat.Prime 3) C.d_pos (by norm_num)
      (hdegree.symm.trans (by norm_num))

/-- Quotient action on the literal transitive block top. -/
def degreeNineWholeQuotientTopMap :
    (preE7NonPairAction w U ⧸ E block P) →* block.Top :=
  PermutationalWreathProduct.rightHom.comp (quotientEmbedding block P)

theorem degreeNineWholeQuotientTopMap_surjective :
    Function.Surjective (degreeNineWholeQuotientTopMap block P) := by
  intro q
  obtain ⟨g, hg⟩ := q.2
  refine ⟨QuotientGroup.mk' (E block P) g, ?_⟩
  change (block.topMap.rangeRestrict g : block.Top) = q
  exact Subtype.ext hg

theorem degreeNineWholeQuotientTopMap_ker :
    (degreeNineWholeQuotientTopMap block P).ker =
      degreeNineLinearBlockKernel block P := by
  rfl

/-! ## Coordinates of the whole linear kernel -/

/-- The literal local coordinates jointly separate the whole actual linear
block kernel. -/
theorem degreeNineLinearBlockKernelCoordinate_joint_injective :
    Function.Injective
      (fun k i => degreeNineLinearBlockKernelCoordinate block P i k) := by
  intro x y hxy
  apply Subtype.ext
  apply quotientEmbedding_injective block P
  apply PermutationalWreathProduct.ext
  · funext i
    exact congrFun hxy i
  · exact (MonoidHom.mem_ker.mp x.2).trans
      (MonoidHom.mem_ker.mp y.2).symm

/-- Ambient conjugation transports one whole-kernel coordinate to the
corresponding transported block. -/
theorem degreeNineLinearBlockKernelCoordinate_conjugation
    (a : preE7NonPairAction w U ⧸ E block P)
    (k : degreeNineLinearBlockKernel block P) (i : block.Points) :
    (degreeNineLinearBlockKernelCoordinate block P
        ((quotientEmbedding block P a).right • i)
        (MulAut.conjNormal a k) : LocalQuotient block P) =
      (quotientEmbedding block P a).left
          ((quotientEmbedding block P a).right • i) *
        degreeNineLinearBlockKernelCoordinate block P i k *
        ((quotientEmbedding block P a).left
          ((quotientEmbedding block P a).right • i))⁻¹ := by
  change (quotientEmbedding block P (a * k.1 * a⁻¹)).left
      ((quotientEmbedding block P a).right • i) =
    (quotientEmbedding block P a).left
        ((quotientEmbedding block P a).right • i) *
      (quotientEmbedding block P k.1).left i *
      ((quotientEmbedding block P a).left
        ((quotientEmbedding block P a).right • i))⁻¹
  rw [map_mul, map_mul, map_inv]
  have hkright : (quotientEmbedding block P k.1).right = 1 :=
    MonoidHom.mem_ker.mp k.2
  simp [PermutationalWreathProduct.mul_left,
    PermutationalWreathProduct.mul_right,
    PermutationalWreathProduct.inv_left, hkright, smul_smul]

/-- Vanishing of one coordinate range forces the whole actual linear block
kernel to vanish. -/
theorem degreeNineLinearBlockKernel_eq_bot_of_coordinate_range_eq_bot
    (i₀ : block.Points)
    (hzero : (degreeNineLinearBlockKernelCoordinate block P i₀).range =
      ⊥) :
    degreeNineLinearBlockKernel block P = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  apply Subgroup.mem_bot.mpr
  let k : degreeNineLinearBlockKernel block P := ⟨x, hx⟩
  have hkone : k = 1 := by
    apply degreeNineLinearBlockKernelCoordinate_joint_injective block P
    funext i
    letI : MulAction.IsPretransitive block.Top block.Points :=
      block.top_pretransitive
    obtain ⟨q, hq⟩ := MulAction.exists_smul_eq block.Top i₀ i
    obtain ⟨a, ha⟩ := degreeNineWholeQuotientTopMap_surjective block P q
    let k₀ : degreeNineLinearBlockKernel block P :=
      MulAut.conjNormal a⁻¹ k
    have hk₀ : degreeNineLinearBlockKernelCoordinate block P i₀ k₀ =
        1 := by
      apply Subtype.ext
      have hmem : degreeNineLinearBlockKernelCoordinate block P i₀ k₀ ∈
          (degreeNineLinearBlockKernelCoordinate block P i₀).range :=
        ⟨k₀, rfl⟩
      rw [hzero] at hmem
      exact congrArg Subtype.val (Subgroup.mem_bot.mp hmem)
    have hconj :=
      degreeNineLinearBlockKernelCoordinate_conjugation block P a k₀ i₀
    have htop : (quotientEmbedding block P a).right • i₀ = i := by
      change degreeNineWholeQuotientTopMap block P a • i₀ = i
      rw [ha]
      exact hq
    have hkconj : MulAut.conjNormal a k₀ = k := by
      apply Subtype.ext
      simp [k₀]
    rw [htop, hkconj, hk₀, mul_one, mul_inv_cancel] at hconj
    simpa only [map_one] using hconj
  exact congrArg Subtype.val hkone

/-- In the nonzero whole-kernel branch every literal coordinate range is
nonzero. -/
theorem degreeNineLinearBlockKernelCoordinate_range_ne_bot_of_kernel_ne_bot
    (hK : degreeNineLinearBlockKernel block P ≠ ⊥)
    (i : block.Points) :
    (degreeNineLinearBlockKernelCoordinate block P i).range ≠ ⊥ := by
  intro hzero
  exact hK (degreeNineLinearBlockKernel_eq_bot_of_coordinate_range_eq_bot
    block P i hzero)

/-! ## The whole literal linear core -/

/-- Preimage in the original action of the whole exact linear block kernel
in `U/E`. -/
abbrev degreeNineWholeCorePreimage :
    Subgroup (preE7NonPairAction w U) :=
  (degreeNineLinearBlockKernel block P).comap
    (QuotientGroup.mk' (E block P))

instance degreeNineWholeCorePreimage_normal :
    (degreeNineWholeCorePreimage block P).Normal := by
  dsimp only [degreeNineWholeCorePreimage]
  infer_instance

theorem degreeNine_translation_le_wholeCorePreimage :
    E block P ≤ degreeNineWholeCorePreimage block P := by
  intro e he
  change QuotientGroup.mk' (E block P) e ∈
    degreeNineLinearBlockKernel block P
  have heone : QuotientGroup.mk' (E block P) e = 1 :=
    (QuotientGroup.eq_one_iff e).mpr he
  simpa only [heone] using
    (Subgroup.one_mem (degreeNineLinearBlockKernel block P))

/-- If the whole linear block kernel vanishes, its original preimage is
exactly the translation intersection. -/
theorem degreeNine_wholeCorePreimage_eq_translation_of_kernel_eq_bot
    (hK : degreeNineLinearBlockKernel block P = ⊥) :
    degreeNineWholeCorePreimage block P = E block P := by
  rw [degreeNineWholeCorePreimage, hK, MonoidHom.comap_bot,
    QuotientGroup.ker_mk']

/-! ## Retained core and literal top section -/

/-- Image of the whole linear-core preimage on a retained normal axis. -/
abbrev degreeNineWholeRetainedCore
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    Subgroup (preE7NonPairAction w U ⧸ N.1) :=
  (degreeNineWholeCorePreimage block P).map (QuotientGroup.mk' N.1)

instance degreeNineWholeRetainedCore_normal
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    (degreeNineWholeRetainedCore block P N).Normal :=
  Subgroup.Normal.map inferInstance (QuotientGroup.mk' N.1)
    (QuotientGroup.mk'_surjective N.1)

theorem degreeNineWholeRetainedCore_eq_translationImage_of_kernel_eq_bot
    (N : LiteralNormalAxis (preE7NonPairAction w U))
    (hK : degreeNineLinearBlockKernel block P = ⊥) :
    degreeNineWholeRetainedCore block P N =
      degreeNineTranslationImage block P N := by
  rw [degreeNineWholeRetainedCore,
    degreeNine_wholeCorePreimage_eq_translation_of_kernel_eq_bot
      block P hK]

/-- Quotient map from `U/N` to the literal block-top section
`U/(ker(top) ⊔ N)`. -/
def degreeNineWholeRetainedTopMap
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    (preE7NonPairAction w U ⧸ N.1) →*
      preE7NonPairAction w U ⧸
        (degreeNineWholeCorePreimage block P ⊔ N.1) :=
  QuotientGroup.lift N.1
    (QuotientGroup.mk' (degreeNineWholeCorePreimage block P ⊔ N.1)) (by
      rw [QuotientGroup.ker_mk']
      exact le_sup_right)

@[simp] theorem degreeNineWholeRetainedTopMap_apply
    (N : LiteralNormalAxis (preE7NonPairAction w U))
    (g : preE7NonPairAction w U) :
    degreeNineWholeRetainedTopMap block P N (QuotientGroup.mk' N.1 g) =
      QuotientGroup.mk' (degreeNineWholeCorePreimage block P ⊔ N.1) g :=
  rfl

theorem degreeNineWholeRetainedTopMap_surjective
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    Function.Surjective (degreeNineWholeRetainedTopMap block P N) := by
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
    (degreeNineWholeCorePreimage block P ⊔ N.1) q
  exact ⟨QuotientGroup.mk' N.1 g, rfl⟩

theorem degreeNineWholeRetainedTopMap_ker
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    (degreeNineWholeRetainedTopMap block P N).ker =
      degreeNineWholeRetainedCore block P N := by
  rw [degreeNineWholeRetainedTopMap, QuotientGroup.ker_lift,
    QuotientGroup.ker_mk', Subgroup.map_sup,
    QuotientGroup.map_mk'_self, sup_bot_eq]

def degreeNineWholeRestrictedTopMap
    (N : LiteralNormalAxis (preE7NonPairAction w U))
    (H : Subgroup (preE7NonPairAction w U ⧸ N.1)) :
    H →* preE7NonPairAction w U ⧸
      (degreeNineWholeCorePreimage block P ⊔ N.1) :=
  (degreeNineWholeRetainedTopMap block P N).comp H.subtype

theorem degreeNineWholeRestrictedTopMap_injective_of_disjoint
    (N : LiteralNormalAxis (preE7NonPairAction w U))
    (H : Subgroup (preE7NonPairAction w U ⧸ N.1))
    (hdisjoint : H ⊓ degreeNineWholeRetainedCore block P N = ⊥) :
    Function.Injective (degreeNineWholeRestrictedTopMap block P N H) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_antisymm
  · intro x hx
    have hxD : (x.1 : preE7NonPairAction w U ⧸ N.1) ∈
        degreeNineWholeRetainedCore block P N := by
      rw [← degreeNineWholeRetainedTopMap_ker block P N]
      exact MonoidHom.mem_ker.mp hx
    have hxInf : (x.1 : preE7NonPairAction w U ⧸ N.1) ∈
        H ⊓ degreeNineWholeRetainedCore block P N := ⟨x.2, hxD⟩
    rw [hdisjoint] at hxInf
    exact Subtype.ext (Subgroup.mem_bot.mp hxInf)
  · exact bot_le

/-- First-isomorphism identification of the quotient by the retained whole
core with the literal block-top section. -/
def degreeNineWholeRetainedCoreQuotientEquivTop
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    ((preE7NonPairAction w U ⧸ N.1) ⧸
        degreeNineWholeRetainedCore block P N) ≃*
      preE7NonPairAction w U ⧸
        (degreeNineWholeCorePreimage block P ⊔ N.1) :=
  (QuotientGroup.quotientMulEquivOfEq
      (degreeNineWholeRetainedTopMap_ker block P N).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (degreeNineWholeRetainedTopMap block P N)
      (degreeNineWholeRetainedTopMap_surjective block P N))

/-! ## The quotient is a literal section of the block top -/

/-- Original action map onto the literal transitive block top. -/
def degreeNineWholeOriginalTopMap :
    preE7NonPairAction w U →* block.Top :=
  (degreeNineWholeQuotientTopMap block P).comp
    (QuotientGroup.mk' (E block P))

theorem degreeNineWholeOriginalTopMap_surjective :
    Function.Surjective (degreeNineWholeOriginalTopMap block P) := by
  intro q
  obtain ⟨g, hg⟩ := q.2
  refine ⟨g, ?_⟩
  change (block.topMap.rangeRestrict g : block.Top) = q
  exact Subtype.ext hg

theorem degreeNineWholeOriginalTopMap_ker :
    (degreeNineWholeOriginalTopMap block P).ker =
      degreeNineWholeCorePreimage block P := by
  rfl

/-- Normal subgroup of the literal block top killed on one retained axis. -/
abbrev degreeNineWholeTopNormalImage
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    Subgroup block.Top :=
  (degreeNineWholeCorePreimage block P ⊔ N.1).map
    (degreeNineWholeOriginalTopMap block P)

instance degreeNineWholeTopNormalImage_normal
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    (degreeNineWholeTopNormalImage block P N).Normal :=
  Subgroup.Normal.map inferInstance
    (degreeNineWholeOriginalTopMap block P)
    (degreeNineWholeOriginalTopMap_surjective block P)

/-- The retained quotient above the whole core is literally a quotient of
the original permutation top. -/
def degreeNineWholeRetainedTopEquivBlockQuotient
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    (preE7NonPairAction w U ⧸
        (degreeNineWholeCorePreimage block P ⊔ N.1)) ≃*
      (block.Top ⧸ degreeNineWholeTopNormalImage block P N) :=
  quotientEquivOfKerLe (degreeNineWholeOriginalTopMap block P)
    (degreeNineWholeOriginalTopMap_surjective block P)
    (degreeNineWholeCorePreimage block P ⊔ N.1) (by
      rw [degreeNineWholeOriginalTopMap_ker block P]
      exact le_sup_left)

/-- Surjection from the literal block top onto the retained top section. -/
def degreeNineWholePermutationTopSectionMap
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    block.Top →*
      preE7NonPairAction w U ⧸
        (degreeNineWholeCorePreimage block P ⊔ N.1) :=
  (degreeNineWholeRetainedTopEquivBlockQuotient block P N).symm.toMonoidHom.comp
    (QuotientGroup.mk' (degreeNineWholeTopNormalImage block P N))

theorem degreeNineWholePermutationTopSectionMap_surjective
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    Function.Surjective
      (degreeNineWholePermutationTopSectionMap block P N) :=
  (degreeNineWholeRetainedTopEquivBlockQuotient block P N).symm.surjective.comp
    (QuotientGroup.mk'_surjective
      (degreeNineWholeTopNormalImage block P N))

/-- Any ambient normal subgroup disjoint from the retained whole core is
faithfully carried by a quotient section of the literal block top. -/
theorem degreeNineWholeCoreDisjoint_normalGen_le
    (hgen : PermutationSubgroupGeneratorBound)
    (hs : 2 ≤ Nat.card block.Points)
    (N : LiteralNormalAxis (preE7NonPairAction w U))
    (H : Subgroup (preE7NonPairAction w U ⧸ N.1)) [H.Normal]
    (hdisjoint : H ⊓ degreeNineWholeRetainedCore block P N = ⊥) :
    MarkedC4.normalGen H ≤ Nat.card block.Points := by
  let pointEquiv : block.Points ≃ Fin (Nat.card block.Points) :=
    Finite.equivFin block.Points
  let τ : block.Top →* Equiv.Perm (Fin (Nat.card block.Points)) :=
    pointEquiv.permCongrHom.toMonoidHom.comp block.Top.subtype
  have hτ : Function.Injective τ :=
    pointEquiv.permCongrHom.injective.comp Subtype.val_injective
  let R : Subgroup (Equiv.Perm (Fin (Nat.card block.Points))) := τ.range
  let eR : block.Top ≃* R := MulEquiv.ofBijective τ.rangeRestrict
    ⟨MonoidHom.rangeRestrict_injective_iff.mpr hτ,
      τ.rangeRestrict_surjective⟩
  let q : R →*
      preE7NonPairAction w U ⧸
        (degreeNineWholeCorePreimage block P ⊔ N.1) :=
    (degreeNineWholePermutationTopSectionMap block P N).comp
      eR.symm.toMonoidHom
  have hq : Function.Surjective q :=
    (degreeNineWholePermutationTopSectionMap_surjective block P N).comp
      eR.symm.surjective
  exact normalGen_normalSubgroup_le_degree_of_permutationSection hgen
    R q hq
    H (degreeNineWholeRestrictedTopMap block P N H)
    (degreeNineWholeRestrictedTopMap_injective_of_disjoint
      block P N H hdisjoint) hs

/-- Every subgroup of the literal transitive block top has the sharp
all-prime permutation character-rank bound. -/
theorem degreeNineWholeBlockTop_primeSectionalRank
    (p : ℕ) [Fact p.Prime] :
    PrimeSectionalRankBound p block.Top
      (Nat.card block.Points / p) := by
  intro K
  simpa only [Fintype.card_eq_nat_card] using
    (permutation_primeCharacterRank_le p K block.Points)

/-- The retained top is a quotient section of the literal block top. -/
theorem degreeNineWholeRetainedTop_primeSectionalRank
    (p : ℕ) [Fact p.Prime]
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    PrimeSectionalRankBound p
      (preE7NonPairAction w U ⧸
        (degreeNineWholeCorePreimage block P ⊔ N.1))
      (Nat.card block.Points / p) := by
  let q : block.Top →*
      block.Top ⧸ degreeNineWholeTopNormalImage block P N :=
    QuotientGroup.mk' (degreeNineWholeTopNormalImage block P N)
  have hquot : PrimeSectionalRankBound p
      (block.Top ⧸ degreeNineWholeTopNormalImage block P N)
      (Nat.card block.Points / p) := by
    intro K
    exact PrimeSectionalRankBound.quotient_rank_le p
      (degreeNineWholeBlockTop_primeSectionalRank block p)
      (K.comap q) (q.subgroupComap K)
      (q.subgroupComap_surjective_of_surjective K
        (QuotientGroup.mk'_surjective
          (degreeNineWholeTopNormalImage block P N)))
  exact PrimeSectionalRankBound.of_injective p hquot
    (degreeNineWholeRetainedTopEquivBlockQuotient block P N).toMonoidHom
    (degreeNineWholeRetainedTopEquivBlockQuotient block P N).injective

/-- Every subgroup of the quotient by the retained whole core inherits the
sharp all-prime sectional rank of the literal block top. -/
theorem degreeNineWholeRetainedCoreQuotient_primeSectionalRank
    (p : ℕ) [Fact p.Prime]
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    PrimeSectionalRankBound p
      ((preE7NonPairAction w U ⧸ N.1) ⧸
        degreeNineWholeRetainedCore block P N)
      (Nat.card block.Points / p) :=
  PrimeSectionalRankBound.of_injective p
    (degreeNineWholeRetainedTop_primeSectionalRank block P p N)
    (degreeNineWholeRetainedCoreQuotientEquivTop block P N).toMonoidHom
    (degreeNineWholeRetainedCoreQuotientEquivTop block P N).injective

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
