import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFourTernaryCatalogueMap
import SymmetricSubgroupAsymptotics.NormalSubgroupOrbitIndex
import SymmetricSubgroupAsymptotics.BinaryCoordinateSplitAction
import SymmetricSubgroupAsymptotics.BinaryPairCoordinateSubgroups
import SymmetricSubgroupAsymptotics.NormalGeneratorTypeSharing

/-!
# The intrinsic four-block set of a ternary count-twelve top

The four-ternary compression uses the actual orbits of the displayed normal
ternary core.  This file identifies that quotient with `Fin 4` from the one
common literal block function.  It is independent of the eight finite rows
and of the binary pair lift above the top.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Pointwise
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

namespace DegreeTwoFourTernaryTopStructure

variable {D : DegreeTwoPairTopFiniteInterface 12}
  (S : DegreeTwoFourTernaryTopStructure D)

/-- The quotient of the twelve literal points by the displayed core
orbits. -/
abbrev OrbitBlocks :=
  MulAction.orbitRel.Quotient S.core (Fin 12)

/-- The same block set realized as the actual orbit, under the whole top,
of the core orbit through zero.  This form carries the natural top action. -/
abbrev Blocks :=
  MulAction.orbit D.top (MulAction.orbit S.core (0 : Fin 12))

/-- The common block label descends to the intrinsic core-orbit quotient. -/
def orbitBlockLabel : S.OrbitBlocks → Fin 4 :=
  Quotient.lift degreeTwoFourTernaryBlock (by
    intro x y hxy
    apply (S.same_block_iff_core_orbit x y).2
    exact MulAction.orbitRel_apply.mp hxy)

@[simp] theorem orbitBlockLabel_mk (x : Fin 12) :
    S.orbitBlockLabel (Quotient.mk'' x) =
      degreeTwoFourTernaryBlock x :=
  rfl

theorem orbitBlockLabel_injective : Function.Injective S.orbitBlockLabel := by
  intro a b hab
  refine Quotient.inductionOn₂ a b ?_
  intro x y hxy
  apply Quotient.sound
  apply MulAction.orbitRel_apply.mpr
  apply (S.same_block_iff_core_orbit x y).1
  simpa only [orbitBlockLabel_mk] using hxy

theorem orbitBlockLabel_surjective : Function.Surjective S.orbitBlockLabel := by
  intro z
  let x : Fin 12 := ⟨z.val, lt_trans z.isLt (by norm_num)⟩
  refine ⟨Quotient.mk'' x, ?_⟩
  apply Fin.ext
  change x.val % 4 = z.val
  exact Nat.mod_eq_of_lt z.isLt

/-- Exact four-coordinate chart of the normal-core orbit quotient. -/
def orbitBlockEquiv : S.OrbitBlocks ≃ Fin 4 :=
  Equiv.ofBijective S.orbitBlockLabel
    ⟨S.orbitBlockLabel_injective, S.orbitBlockLabel_surjective⟩

/-- Exact four-coordinate chart of the actual top block orbit. -/
def blockEquiv : S.Blocks ≃ Fin 4 :=
  (normalOrbitClassesEquivBlockOrbit S.core (0 : Fin 12)).symm.trans
    S.orbitBlockEquiv

theorem orbitBlocks_card : Nat.card S.OrbitBlocks = 4 :=
  Nat.card_congr S.orbitBlockEquiv

theorem blocks_card : Nat.card S.Blocks = 4 :=
  Nat.card_congr S.blockEquiv

/-- Sum a binary vector on one member of the actual top orbit of ternary
blocks.  Using the acted-on block set here keeps every later equivariance
and kernel statement free of quotient-representative transport. -/
def blockOrbitParity :
    (Fin 12 → ZMod 2) →ₗ[ZMod 2] (S.Blocks → ZMod 2) where
  toFun v B := ∑ x : B.1, v x.1
  map_add' _ _ := by
    funext B
    exact Finset.sum_add_distrib
  map_smul' _ _ := by
    funext B
    simp only [Pi.smul_apply, Finset.smul_sum, RingHom.id_apply]

/-- Its kernel is the direct sum of the four two-dimensional ternary
augmentation planes.  Keeping it as a literal kernel avoids selecting any
basis or independent coordinate columns. -/
def augmentationPlanes : Submodule (ZMod 2) (Fin 12 → ZMod 2) :=
  S.blockOrbitParity.ker

@[simp] theorem mem_augmentationPlanes (v : Fin 12 → ZMod 2) :
    v ∈ S.augmentationPlanes ↔
      ∀ B : S.Blocks, ∑ x : B.1, v x.1 = 0 := by
  rw [augmentationPlanes, LinearMap.mem_ker]
  constructor
  · intro h B
    exact congrFun h B
  · intro h B
    exact h B

/-- Literal translation of one actual ternary block by a top element. -/
def blockTranslationEquiv (g : D.top) (B : S.Blocks) :
    B.1 ≃ (g • B).1 where
  toFun x := ⟨g • x.1, Set.smul_mem_smul_set x.2⟩
  invFun x := ⟨g⁻¹ • x.1, by
    have hx : g⁻¹ • x.1 ∈ g⁻¹ • (g • (B : Set (Fin 12))) :=
      Set.smul_mem_smul_set x.2
    simpa only [← mul_smul, inv_mul_cancel, one_smul] using hx⟩
  left_inv x := Subtype.ext (inv_smul_smul g x.1)
  right_inv x := Subtype.ext (smul_inv_smul g x.1)

/-- Block parity intertwines the natural permutation actions. -/
theorem blockOrbitParity_action
    (g : D.top) (v : Fin 12 → ZMod 2) (B : S.Blocks) :
    S.blockOrbitParity
        (permutationFunctionRepresentation (ZMod 2) D.top (Fin 12) g v)
        (g • B) =
      S.blockOrbitParity v B := by
  have h := Equiv.sum_comp (S.blockTranslationEquiv g B)
    (fun x : (g • B).1 =>
      permutationFunctionRepresentation (ZMod 2) D.top (Fin 12) g v x.1)
  change (∑ x : B.1, v (g⁻¹ • (g • x.1))) =
    ∑ y : (g • B).1, v (g⁻¹ • y.1) at h
  simpa only [inv_smul_smul] using h.symm

/-- Normality of the ternary core makes the four augmentation planes a
subrepresentation of the actual natural top module. -/
def augmentationRepresentation : Subrepresentation
    (permutationFunctionRepresentation (ZMod 2) D.top (Fin 12)) where
  toSubmodule := S.augmentationPlanes
  apply_mem_toSubmodule g v hv := by
    apply (S.mem_augmentationPlanes _).2
    intro B
    have hparity := S.blockOrbitParity_action g v (g⁻¹ • B)
    calc
      S.blockOrbitParity
          (permutationFunctionRepresentation (ZMod 2) D.top (Fin 12) g v) B =
          S.blockOrbitParity v (g⁻¹ • B) := by
            simpa only [smul_inv_smul] using hparity
      _ = 0 := (S.mem_augmentationPlanes v).1 hv (g⁻¹ • B)

/-- Transport the same literal subspace to the coordinate action of an
arbitrary original pair realization.  No split lift is selected. -/
def realizedAugmentationRepresentation
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p) :
    Subrepresentation R.frame.coordinateTopAction where
  toSubmodule := S.augmentationPlanes
  apply_mem_toSubmodule t v hv := by
    let g : D.top := R.topEquiv.symm t
    have h := (S.augmentationRepresentation).apply_mem_toSubmodule g hv
    change R.frame.coordinateTopAction t v ∈ S.augmentationPlanes
    rw [← R.topEquiv.apply_symm_apply t]
    rw [← R.module_action_eq g v]
    exact h

/-- The literal degree-twelve top of one actual pair realization. -/
def realizedTop
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p) :
    preE7PairAction 12 p →* D.top :=
  R.topEquiv.symm.toMonoidHom.comp R.frame.top.rangeRestrict

/-- The exact averaging subgroup in the original pair lift.  It is the
intersection of the actual correlated pair kernel with the four ternary
augmentation planes. -/
def averagingSubgroup
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p) :
    Subgroup (preE7PairAction 12 p) :=
  R.frame.coordinateSubgroup
    (S.realizedAugmentationRepresentation R).toSubmodule

noncomputable instance averagingSubgroup_normal
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p) :
    (S.averagingSubgroup R).Normal :=
  R.frame.coordinateSubgroup_normal
    (S.realizedAugmentationRepresentation R)

/-- Full preimage in the original pair lift of the displayed ternary core
of its literal top. -/
def ternaryPreimage
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p) :
    Subgroup (preE7PairAction 12 p) :=
  S.core.comap (S.realizedTop R)

noncomputable instance ternaryPreimage_normal
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p) :
    (S.ternaryPreimage R).Normal :=
  Subgroup.Normal.comap inferInstance (S.realizedTop R)

/-- Image of the full ternary preimage in one literal retained quotient. -/
def retainedTernaryImage
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : {N : Subgroup (preE7PairAction 12 p) // N.Normal}) :
    Subgroup (preE7PairAction 12 p ⧸ N.1) :=
  (S.ternaryPreimage R).map (QuotientGroup.mk' N.1)

noncomputable instance retainedTernaryImage_normal
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : {N : Subgroup (preE7PairAction 12 p) // N.Normal}) :
    (S.retainedTernaryImage R N).Normal :=
  Subgroup.Normal.map inferInstance (QuotientGroup.mk' N.1)
    (QuotientGroup.mk'_surjective N.1)

/-- The retained parity translation on the four actual ternary blocks. -/
def realizedBlockTranslation
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (u : preE7PairAction 12 p) : S.Blocks → ZMod 2 :=
  S.blockOrbitParity (R.frame.affineTranslation u)

/-- The block-parity translation is the image of the original pair
cocycle.  This identity is the nonsplit-safe heart of the averaging map. -/
theorem realizedBlockTranslation_mul
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (u v : preE7PairAction 12 p) :
    S.realizedBlockTranslation R (u * v) =
      permutationFunctionRepresentation (ZMod 2) D.top S.Blocks
          (S.realizedTop R u) (S.realizedBlockTranslation R v) +
        S.realizedBlockTranslation R u := by
  funext B
  rw [realizedBlockTranslation, R.frame.affineTranslation_mul, map_add]
  change S.blockOrbitParity
      (R.frame.coordinateTopAction (R.frame.top.rangeRestrict u)
        (R.frame.affineTranslation v)) B + _ = _
  let g : D.top := S.realizedTop R u
  have htop : R.topEquiv g = R.frame.top.rangeRestrict u := by
    exact R.topEquiv.apply_symm_apply _
  rw [← htop, ← R.module_action_eq g (R.frame.affineTranslation v)]
  have hparity := S.blockOrbitParity_action g
    (R.frame.affineTranslation v) (g⁻¹ • B)
  simpa only [smul_inv_smul] using congrArg (fun z => z +
    S.realizedBlockTranslation R u B) hparity

/-- The actual affine action on the eight block-bit points. -/
def blockAffineAction
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p) :
    preE7PairAction 12 p →* Equiv.Perm (S.Blocks × ZMod 2) where
  toFun u := binaryCoordinateAffinePermutation
    (MulAction.toPermHom D.top S.Blocks (S.realizedTop R u))
    (S.realizedBlockTranslation R u)
  map_one' := by
    apply Equiv.ext
    rintro ⟨B, b⟩
    simp only [binaryCoordinateAffinePermutation, map_one,
      Equiv.Perm.one_apply, S.realizedBlockTranslation,
      R.frame.affineTranslation_one, map_zero, Pi.zero_apply, add_zero]
  map_mul' u v := by
    apply Equiv.ext
    rintro ⟨B, b⟩
    apply Prod.ext
    · simp only [binaryCoordinateAffinePermutation, map_mul,
        Equiv.Perm.mul_apply]
    · change b + S.realizedBlockTranslation R (u * v)
          (S.realizedTop R (u * v) • B) =
        (b + S.realizedBlockTranslation R v
          (S.realizedTop R v • B)) +
          S.realizedBlockTranslation R u
            (S.realizedTop R u • (S.realizedTop R v • B))
      rw [S.realizedBlockTranslation_mul R u v]
      simp only [Pi.add_apply,
        permutationFunctionRepresentation_apply, map_mul, mul_smul]
      abel

/-- Relabel the four actual blocks and their binary bits by eight standard
points. -/
def blockPointEquiv : S.Blocks × ZMod 2 ≃ Fin 8 :=
  (Equiv.prodCongr S.blockEquiv (ZMod.finEquiv 2).symm.toEquiv).trans
    finProdFinEquiv

/-- Relabel the disjoint union of the twelve top labels and eight block-bit
labels by twenty standard points. -/
def compressedPointEquiv : Fin 12 ⊕ (S.Blocks × ZMod 2) ≃ Fin 20 :=
  (Equiv.sumCongr (Equiv.refl (Fin 12)) S.blockPointEquiv).trans
    finSumFinEquiv

/-- The degree-twenty action before passing to the averaging quotient.  It
is the disjoint sum of the original top labels and the four block-bit
coordinates. -/
def compressedAction
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p) :
    preE7PairAction 12 p →* Equiv.Perm (Fin 20) :=
  S.compressedPointEquiv.permCongrHom.toMonoidHom.comp
    ((Equiv.Perm.sumCongrHom (Fin 12) (S.Blocks × ZMod 2)).comp
      (R.frame.top.prodMap (S.blockAffineAction R)))

theorem compressedAction_ker
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p) :
    (S.compressedAction R).ker = S.averagingSubgroup R := by
  ext u
  rw [MonoidHom.mem_ker]
  constructor
  · intro hu
    have hsum :
        (Equiv.Perm.sumCongrHom (Fin 12) (S.Blocks × ZMod 2))
            (R.frame.top.prodMap (S.blockAffineAction R) u) = 1 := by
      apply S.compressedPointEquiv.permCongrHom.injective
      rw [map_one]
      exact hu
    have hpair := Equiv.Perm.sumCongrHom_injective
      (hsum.trans (map_one _).symm)
    have htop : R.frame.top u = 1 := congrArg Prod.fst hpair
    have hblock : S.blockAffineAction R u = 1 := congrArg Prod.snd hpair
    have hrange : R.frame.top.rangeRestrict u = 1 := Subtype.ext htop
    have hrealizedTop : S.realizedTop R u = 1 := by
      change R.topEquiv.symm (R.frame.top.rangeRestrict u) = 1
      rw [hrange, map_one]
    let k : R.frame.top.ker := ⟨u, htop⟩
    apply (R.frame.kernel_mem_coordinateSubgroup
      (S.realizedAugmentationRepresentation R).toSubmodule k).2
    change R.frame.bits k ∈ S.augmentationPlanes
    apply (S.mem_augmentationPlanes _).2
    intro B
    have hb' := congrArg (fun f : Equiv.Perm (S.Blocks × ZMod 2) =>
      f (B, 0)) hblock
    have hz : S.realizedBlockTranslation R u B = 0 := by
      simpa only [blockAffineAction, binaryCoordinateAffinePermutation,
        hrealizedTop, map_one, Equiv.Perm.one_apply, zero_add]
        using congrArg Prod.snd hb'
    rw [realizedBlockTranslation, R.frame.affineTranslation_kernel k] at hz
    exact hz
  · intro hu
    have hutop : R.frame.top u = 1 :=
      R.frame.coordinateSubgroup_le_kernel
        (S.realizedAugmentationRepresentation R).toSubmodule hu
    have hrange : R.frame.top.rangeRestrict u = 1 := Subtype.ext hutop
    have hrealizedTop : S.realizedTop R u = 1 := by
      change R.topEquiv.symm (R.frame.top.rangeRestrict u) = 1
      rw [hrange, map_one]
    let k : R.frame.top.ker := ⟨u, hutop⟩
    have hk := (R.frame.kernel_mem_coordinateSubgroup
      (S.realizedAugmentationRepresentation R).toSubmodule k).1 hu
    have hparity : S.realizedBlockTranslation R u = 0 := by
      funext B
      rw [realizedBlockTranslation, R.frame.affineTranslation_kernel k]
      exact (S.mem_augmentationPlanes _).1 hk B
    apply S.compressedPointEquiv.permCongrHom.injective
    rw [map_one]
    apply Equiv.Perm.sumCongrHom_injective
    apply Prod.ext hutop
    apply Equiv.ext
    rintro ⟨B, b⟩
    simp only [blockAffineAction, binaryCoordinateAffinePermutation,
      hrealizedTop, hparity, map_one, Equiv.Perm.one_apply, Pi.zero_apply,
      add_zero]

/-- The only remaining group-theoretic statement after the uniform
block-parity construction: every original quotient which sees a nonzero
augmentation plane has whole socle normally generated in three positions. -/
def RetainedSocleTheorem : Prop :=
  ∀ (p : PreE7PairActionClass 12)
    (R : DegreeTwoPairTopRealization D p)
    (N : {N : Subgroup (preE7PairAction 12 p) // N.Normal}),
    ¬ S.averagingSubgroup R ≤ N.1 →
      SocleNormalGeneratorBound (preE7PairAction 12 p ⧸ N.1) 3

/-- The two concrete estimates left by the four-ternary module argument.
The moving part costs at most two positions; the core-central part costs at
most three.  The generic action-type Goursat theorem shares these positions
instead of adding them. -/
structure RetainedSoclePartsBounds : Prop where
  active : ∀ (p : PreE7PairActionClass 12)
    (R : DegreeTwoPairTopRealization D p)
    (N : {N : Subgroup (preE7PairAction 12 p) // N.Normal}),
    ¬ S.averagingSubgroup R ≤ N.1 →
      MarkedC4.normalGen
        (nontrivialActionSoclePart (preE7PairAction 12 p ⧸ N.1)
          (S.retainedTernaryImage R N)) ≤ 2
  fixed : ∀ (p : PreE7PairActionClass 12)
    (R : DegreeTwoPairTopRealization D p)
    (N : {N : Subgroup (preE7PairAction 12 p) // N.Normal}),
    ¬ S.averagingSubgroup R ≤ N.1 →
      MarkedC4.normalGen
        (trivialActionSoclePart (preE7PairAction 12 p ⧸ N.1)
          (S.retainedTernaryImage R N)) ≤ 3

/-- Type-sharing turns the `2/3` part bounds into the required three-slot
whole-socle theorem. -/
theorem retainedSocleTheorem_of_parts
    (H : S.RetainedSoclePartsBounds) :
    S.RetainedSocleTheorem := by
  intro p R N hN
  apply (socleNormalGeneratorBound_iff_normalGen_le _ _).2
  let C := S.retainedTernaryImage R N
  have hmax := normalGen_finiteGroupSocle_le_max_actionSocleParts
    (preE7PairAction 12 p ⧸ N.1) C
  exact hmax.trans (max_le ((H.active p R N hN).trans (by norm_num))
    (H.fixed p R N hN))

/-- Assemble the exact-kernel certificate from the remaining whole-socle
statement. -/
noncomputable def compressionCertificate
    (hsocle : S.RetainedSocleTheorem)
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p) :
    DegreeTwoFourTernaryCompressionCertificate p where
  E := S.averagingSubgroup R
  compressedAction := S.compressedAction R
  compressedAction_ker := S.compressedAction_ker R
  quotientSocleGenerators := fun N hN => hsocle p R N hN

/-- Hence the entire reusable compression theorem has now been reduced to
the single, action-theoretic socle assertion above. -/
theorem certificateTheorem_of_retainedSocle
    (hsocle : S.RetainedSocleTheorem) :
    S.CertificateTheorem := by
  intro p R
  exact ⟨S.compressionCertificate hsocle R⟩

theorem compressionTheorem_of_retainedSocle
    (hsocle : S.RetainedSocleTheorem) :
    S.CompressionTheorem :=
  S.compressionTheorem_of_certificate
    (S.certificateTheorem_of_retainedSocle hsocle)

end DegreeTwoFourTernaryTopStructure

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
