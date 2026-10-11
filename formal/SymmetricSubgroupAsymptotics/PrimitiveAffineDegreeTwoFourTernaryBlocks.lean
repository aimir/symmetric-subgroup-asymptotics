import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFourTernaryStructure
import SymmetricSubgroupAsymptotics.NormalSubgroupOrbitIndex
import SymmetricSubgroupAsymptotics.BinaryCoordinateSplitAction
import SymmetricSubgroupAsymptotics.BinaryPairCoordinateSubgroups
import SymmetricSubgroupAsymptotics.NormalGeneratorTypeSharing
import SymmetricSubgroupAsymptotics.FiniteSocleNormalGenerators
import SymmetricSubgroupAsymptotics.ZmudFaithfulCharacterInput
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

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

noncomputable local instance : S.core.Normal := S.core_normal

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
    exact ((S.same_block_iff_core_orbit y x).2 hxy).symm)

@[simp] theorem orbitBlockLabel_mk (x : Fin 12) :
    S.orbitBlockLabel (Quotient.mk'' x) =
      degreeTwoFourTernaryBlock x :=
  rfl

theorem orbitBlockLabel_injective : Function.Injective S.orbitBlockLabel := by
  intro a b hab
  exact Quotient.inductionOn₂ a b (fun x y hxy ↦ by
    apply Quotient.sound
    apply MulAction.orbitRel_apply.mpr
    apply (S.same_block_iff_core_orbit y x).1
    simpa only [orbitBlockLabel_mk] using hxy.symm) hab

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
def blockEquiv : S.Blocks ≃ Fin 4 := by
  letI : MulAction.IsPretransitive D.top (Fin 12) := S.top_transitive
  exact (normalOrbitClassesEquivBlockOrbit S.core (0 : Fin 12)).symm.trans
    S.orbitBlockEquiv

theorem orbitBlocks_card : Nat.card S.OrbitBlocks = 4 :=
  by simpa using Nat.card_congr S.orbitBlockEquiv

theorem blocks_card : Nat.card S.Blocks = 4 :=
  by simpa using Nat.card_congr S.blockEquiv

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
  · intro h
    funext B
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
  by
    let _S := S
    exact R.topEquiv.symm.toMonoidHom.comp R.frame.top.rangeRestrict

/-- The actual correlated part of the four ternary augmentation planes. -/
def averagingCoordinateRepresentation
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p) :
    Subrepresentation R.frame.coordinateTopAction :=
  S.realizedAugmentationRepresentation R ⊓ R.frame.kernelSubrepresentation

/-- The exact averaging subgroup in the original pair lift. -/
def averagingSubgroup
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p) :
    Subgroup (preE7PairAction 12 p) :=
  R.frame.coordinateSubgroup
    (S.averagingCoordinateRepresentation R).toSubmodule

noncomputable instance averagingSubgroup_normal
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p) :
    (S.averagingSubgroup R).Normal :=
  R.frame.coordinateSubgroup_normal
    (S.averagingCoordinateRepresentation R)

/-- Exact binary coordinates on the correlated averaging subgroup. -/
noncomputable def averagingCoordinateEquiv
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p) :
    S.averagingSubgroup R ≃*
      Multiplicative (S.averagingCoordinateRepresentation R).toSubmodule := by
  let W := (S.averagingCoordinateRepresentation R).toSubmodule
  have hW : W ≤ R.frame.kernelSpace := fun _ hv ↦ hv.2
  let e : R.frame.coordinateKernelSubgroup W ≃* S.averagingSubgroup R :=
    (R.frame.coordinateKernelSubgroup W).equivMapOfInjective
      R.frame.top.ker.subtype Subtype.val_injective
  let f : R.frame.coordinateKernelSubgroup W ≃* Multiplicative W :=
    MulEquiv.ofBijective (R.frame.coordinateKernelHom W)
      (R.frame.coordinateKernelHom_bijective W hW)
  exact e.symm.trans f

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
    have htop : S.realizedTop R 1 = 1 := map_one _
    have htranslation : S.realizedBlockTranslation R 1 = 0 := by
      funext B
      rw [realizedBlockTranslation, R.frame.affineTranslation_one, map_zero]
    change (S.realizedTop R 1 • B,
      b + S.realizedBlockTranslation R 1 (S.realizedTop R 1 • B)) = (B, b)
    rw [htop, htranslation]
    simp only [one_smul, Pi.zero_apply, add_zero]
  map_mul' u v := by
    apply Equiv.ext
    rintro ⟨B, b⟩
    apply Prod.ext
    · change S.realizedTop R (u * v) • B =
        S.realizedTop R u • (S.realizedTop R v • B)
      simp only [map_mul, mul_smul]
    · change b + S.realizedBlockTranslation R (u * v)
          (S.realizedTop R (u * v) • B) =
        (b + S.realizedBlockTranslation R v
          (S.realizedTop R v • B)) +
          S.realizedBlockTranslation R u
            (S.realizedTop R u • (S.realizedTop R v • B))
      rw [S.realizedBlockTranslation_mul R u v]
      simp only [Pi.add_apply,
        permutationFunctionRepresentation_apply, map_mul, mul_smul,
        inv_smul_smul]
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
      (R.frame.top.prod (S.blockAffineAction R)))

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
            (R.frame.top.prod (S.blockAffineAction R) u) = 1 := by
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
      (S.averagingCoordinateRepresentation R).toSubmodule k).2
    refine ⟨?_, ?_⟩
    · apply (S.mem_augmentationPlanes _).2
      intro B
      have hb' := congrArg (fun f : Equiv.Perm (S.Blocks × ZMod 2) =>
        f (B, 0)) hblock
      have hz : S.realizedBlockTranslation R u B = 0 := by
        have hz' := congrArg Prod.snd hb'
        change 0 + S.realizedBlockTranslation R u
          (S.realizedTop R u • B) = 0 at hz'
        simpa only [hrealizedTop, one_smul, zero_add] using hz'
      rw [realizedBlockTranslation, R.frame.affineTranslation_kernel k] at hz
      exact hz
    · exact ⟨Additive.ofMul k, rfl⟩
  · intro hu
    have hutop : R.frame.top u = 1 :=
      R.frame.coordinateSubgroup_le_kernel
        (S.averagingCoordinateRepresentation R).toSubmodule hu
    have hrange : R.frame.top.rangeRestrict u = 1 := Subtype.ext hutop
    have hrealizedTop : S.realizedTop R u = 1 := by
      change R.topEquiv.symm (R.frame.top.rangeRestrict u) = 1
      rw [hrange, map_one]
    let k : R.frame.top.ker := ⟨u, hutop⟩
    have hk := (R.frame.kernel_mem_coordinateSubgroup
      (S.averagingCoordinateRepresentation R).toSubmodule k).1 hu
    have hparity : S.realizedBlockTranslation R u = 0 := by
      funext B
      rw [realizedBlockTranslation, R.frame.affineTranslation_kernel k]
      exact (S.mem_augmentationPlanes _).1 hk.1 B
    change S.compressedPointEquiv.permCongrHom
        ((Equiv.Perm.sumCongrHom (Fin 12) (S.Blocks × ZMod 2))
          (R.frame.top u, S.blockAffineAction R u)) = 1
    rw [← map_one S.compressedPointEquiv.permCongrHom]
    apply congrArg S.compressedPointEquiv.permCongrHom
    rw [← map_one (Equiv.Perm.sumCongrHom (Fin 12)
      (S.Blocks × ZMod 2))]
    apply congrArg (Equiv.Perm.sumCongrHom (Fin 12)
      (S.Blocks × ZMod 2))
    apply Prod.ext hutop
    apply Equiv.ext
    rintro ⟨B, b⟩
    change (S.realizedTop R u • B,
      b + S.realizedBlockTranslation R u (S.realizedTop R u • B)) =
      (B, b)
    rw [hrealizedTop, hparity]
    simp only [one_smul, Pi.zero_apply, add_zero]

/-! ## The active four-plane socle -/

/-- The image of the actual correlated four-plane subgroup in a retained
quotient.  Naming the literal image keeps the active-socle statements below
independent of any choice of coordinates on the quotient. -/
def retainedAveragingImage
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : {N : Subgroup (preE7PairAction 12 p) // N.Normal}) :
    Subgroup (preE7PairAction 12 p ⧸ N.1) :=
  (S.averagingSubgroup R).map (QuotientGroup.mk' N.1)

noncomputable instance retainedAveragingImage_normal
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : {N : Subgroup (preE7PairAction 12 p) // N.Normal}) :
    (S.retainedAveragingImage R N).Normal :=
  Subgroup.Normal.map inferInstance (QuotientGroup.mk' N.1)
    (QuotientGroup.mk'_surjective N.1)

/-- Every element of the displayed ternary core fixes every one of its four
orbits setwise. -/
theorem core_smul_block (c : S.core) (B : S.Blocks) :
    (c.1 : D.top) • B = B := by
  obtain ⟨g, hg⟩ := B.property
  apply Subtype.ext
  change c.1 • (B : Set (Fin 12)) = (B : Set (Fin 12))
  rw [← hg]
  change c.1 • (g • MulAction.orbit S.core (0 : Fin 12)) =
    g • MulAction.orbit S.core (0 : Fin 12)
  rw [← mul_smul, show c.1 * g = g * (g⁻¹ * c.1 * g) by group, mul_smul]
  congr 1
  rw [MulAction.smul_orbit_eq_orbit_smul]
  apply MulAction.orbit_eq_iff.mpr
  refine ⟨⟨g⁻¹ * c.1 * g, ?_⟩, rfl⟩
  exact S.core_normal.conj_mem c.1 c.2 g⁻¹

/-- On the ternary preimage, the block-bit affine permutations commute:
the core fixes the four block labels, while the remaining translations add
in the abelian binary fibres. -/
theorem blockAffineAction_commute_on_ternaryPreimage
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (u v : preE7PairAction 12 p)
    (hu : u ∈ S.ternaryPreimage R)
    (hv : v ∈ S.ternaryPreimage R) :
    Commute (S.blockAffineAction R u) (S.blockAffineAction R v) := by
  rw [commute_iff_eq]
  apply Equiv.ext
  rintro ⟨B, b⟩
  have huB : S.realizedTop R u • B = B :=
    S.core_smul_block ⟨S.realizedTop R u, hu⟩ B
  have hvB : S.realizedTop R v • B = B :=
    S.core_smul_block ⟨S.realizedTop R v, hv⟩ B
  change
    (S.realizedTop R u • (S.realizedTop R v • B),
      (b + S.realizedBlockTranslation R v
        (S.realizedTop R v • B)) +
        S.realizedBlockTranslation R u
          (S.realizedTop R u • (S.realizedTop R v • B))) =
    (S.realizedTop R v • (S.realizedTop R u • B),
      (b + S.realizedBlockTranslation R u
        (S.realizedTop R u • B)) +
        S.realizedBlockTranslation R v
          (S.realizedTop R v • (S.realizedTop R u • B)))
  simp only [huB, hvB]
  apply Prod.ext
  · rfl
  · abel

/-- The full degree-twenty compressed image of the ternary preimage is
abelian.  This is the nonsplit-safe commutator statement: it uses the
literal top action and the four block parities simultaneously. -/
theorem compressedAction_commute_on_ternaryPreimage
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (u v : preE7PairAction 12 p)
    (hu : u ∈ S.ternaryPreimage R)
    (hv : v ∈ S.ternaryPreimage R) :
    Commute (S.compressedAction R u) (S.compressedAction R v) := by
  have hcore : Commute (S.realizedTop R u) (S.realizedTop R v) :=
    congrArg Subtype.val
      ((isMulCommutative_iff.mp S.core_commutative)
        ⟨S.realizedTop R u, hu⟩
        ⟨S.realizedTop R v, hv⟩)
  have htopRange : Commute (R.frame.top.rangeRestrict u)
      (R.frame.top.rangeRestrict v) := by
    have h := hcore.map R.topEquiv.toMonoidHom
    change Commute
      (R.topEquiv (R.topEquiv.symm (R.frame.top.rangeRestrict u)))
      (R.topEquiv (R.topEquiv.symm (R.frame.top.rangeRestrict v))) at h
    simpa only [R.topEquiv.apply_symm_apply] using h
  have htop : Commute (R.frame.top u) (R.frame.top v) :=
    congrArg Subtype.val htopRange.eq
  have hblock := S.blockAffineAction_commute_on_ternaryPreimage R u v hu hv
  have hpair : Commute
      (R.frame.top u, S.blockAffineAction R u)
      (R.frame.top v, S.blockAffineAction R v) := by
    exact Prod.ext htop.eq hblock.eq
  exact (hpair.map
    (Equiv.Perm.sumCongrHom (Fin 12) (S.Blocks × ZMod 2))).map
      S.compressedPointEquiv.permCongrHom.toMonoidHom

/-- The ternary preimage has commutator inside the exact correlated
four-plane subgroup. -/
theorem ternaryPreimage_commutator_le_averagingSubgroup
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p) :
    ⁅S.ternaryPreimage R, S.ternaryPreimage R⁆ ≤
      S.averagingSubgroup R := by
  rw [← S.compressedAction_ker R, Subgroup.commutator_le]
  intro u hu v hv
  apply MonoidHom.mem_ker.mpr
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr
    (S.compressedAction_commute_on_ternaryPreimage R u v hu hv).eq

/-- The retained ternary image is abelian modulo the retained averaging
image in every original quotient. -/
theorem retainedTernaryImage_commutator_le_retainedAveragingImage
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : {N : Subgroup (preE7PairAction 12 p) // N.Normal}) :
    ⁅S.retainedTernaryImage R N, S.retainedTernaryImage R N⁆ ≤
      S.retainedAveragingImage R N := by
  rw [retainedTernaryImage, retainedAveragingImage,
    ← Subgroup.map_commutator]
  exact Subgroup.map_mono
    (S.ternaryPreimage_commutator_le_averagingSubgroup R)

/-- Every ambient-minimal factor on which the retained ternary image acts
nontrivially is physically carried by the retained four-plane image. -/
theorem minimalNormal_active_le_retainedAveragingImage
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : {N : Subgroup (preE7PairAction 12 p) // N.Normal})
    (M : Subgroup (preE7PairAction 12 p ⧸ N.1))
    (hactive : ⁅S.retainedTernaryImage R N, M⁆ = M) :
    M ≤ S.retainedAveragingImage R N := by
  have hMC : M ≤ S.retainedTernaryImage R N := by
    rw [← hactive]
    exact Subgroup.commutator_le_left _ _
  rw [← hactive]
  exact (Subgroup.commutator_mono le_rfl hMC).trans
    (S.retainedTernaryImage_commutator_le_retainedAveragingImage R N)

/-- The whole active socle part is carried by the actual retained
four-plane image. -/
theorem nontrivialActionSoclePart_le_retainedAveragingImage
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : {N : Subgroup (preE7PairAction 12 p) // N.Normal}) :
    nontrivialActionSoclePart (preE7PairAction 12 p ⧸ N.1)
        (S.retainedTernaryImage R N) ≤
      S.retainedAveragingImage R N := by
  unfold nontrivialActionSoclePart minimalNormalSoclePart
  apply Finset.sup_le
  intro M hM
  exact S.minimalNormal_active_le_retainedAveragingImage R N M
    (Finset.mem_filter.mp hM).2.2

/-- Restrict a literal four-plane vector to each actual core orbit.  The
codomain remembers the zero-sum equation separately on every orbit. -/
def orbitCoordinateSum (o : S.OrbitBlocks) :
    (o.orbit → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun v := ∑ x, v x
  map_add' _ _ := Finset.sum_add_distrib
  map_smul' _ _ := by
    simp only [Pi.smul_apply, Finset.smul_sum, RingHom.id_apply]

def orbitAugmentationSpace (o : S.OrbitBlocks) :
    Submodule (ZMod 2) (o.orbit → ZMod 2) :=
  (S.orbitCoordinateSum o).ker

def augmentationOrbitRestriction :
    S.augmentationPlanes →
      (o : S.OrbitBlocks) →
        S.orbitAugmentationSpace o := fun v o =>
  ⟨fun x => v.1 x.1, by
    letI : MulAction.IsPretransitive D.top (Fin 12) := S.top_transitive
    let B : S.Blocks := normalOrbitClassesEquivBlockOrbit S.core
      (0 : Fin 12) o
    change (S.orbitCoordinateSum o) (fun x => v.1 x.1) = 0
    simpa only [B] using (S.mem_augmentationPlanes v.1).1 v.2 B⟩

theorem augmentationOrbitRestriction_injective :
    Function.Injective S.augmentationOrbitRestriction := by
  intro v w hvw
  apply Subtype.ext
  funext x
  let o : S.OrbitBlocks := Quotient.mk'' x
  let xo : o.orbit :=
    ⟨x, (MulAction.orbitRel.Quotient.mem_orbit).mpr rfl⟩
  exact congrArg (fun f => (f o : o.orbit → ZMod 2) xo) hvw

/-- Each of the four displayed core orbits has exactly three points. -/
theorem orbit_card_eq_three (o : S.OrbitBlocks) : Nat.card o.orbit = 3 := by
  letI : MulAction.IsPretransitive D.top (Fin 12) := S.top_transitive
  have hbase := normal_orbit_card_mul_classes S.core (0 : Fin 12)
  rw [S.orbitBlocks_card] at hbase
  have hbaseCard : Nat.card (MulAction.orbit S.core (0 : Fin 12)) = 3 := by
    have hfin : Nat.card (Fin 12) = 12 := by simp
    rw [hfin] at hbase
    omega
  exact (normal_orbit_card_eq S.core (0 : Fin 12) o).trans hbaseCard

/-- One binary zero-sum plane on a ternary orbit has four elements. -/
theorem orbitAugmentation_card_eq_four (o : S.OrbitBlocks) :
    Nat.card (S.orbitAugmentationSpace o) = 4 := by
  have hsurj : Function.Surjective (S.orbitCoordinateSum o) := by
    intro c
    refine ⟨fun _ ↦ c, ?_⟩
    simp only [orbitCoordinateSum, LinearMap.coe_mk, AddHom.coe_mk,
      Finset.sum_const, Finset.card_univ, Fintype.card_eq_nat_card,
      S.orbit_card_eq_three o]
    have htwo : ∀ x : ZMod 2, 2 • x = 0 := by decide
    rw [show (3 : ℕ) = 2 + 1 by norm_num, add_nsmul, htwo c,
      zero_add, one_nsmul]
  have hrange : LinearMap.range (S.orbitCoordinateSum o) = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have hdim := (S.orbitCoordinateSum o).finrank_range_add_finrank_ker
  rw [hrange, finrank_top, Module.finrank_self,
    Module.finrank_pi, Fintype.card_eq_nat_card,
    S.orbit_card_eq_three o] at hdim
  have hfinrank : Module.finrank (ZMod 2)
      (S.orbitAugmentationSpace o) = 2 := by
    simpa only [orbitAugmentationSpace] using (show
      Module.finrank (ZMod 2) (S.orbitCoordinateSum o).ker = 2 by omega)
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    hfinrank]
  norm_num

/-- The direct sum of the four ternary augmentation planes has at most
`4^4 = 256` elements.  The orbit-restriction map is in fact an equivalence,
but injectivity is the only direction needed for the generator bound. -/
theorem augmentationPlanes_card_le : Nat.card S.augmentationPlanes ≤ 256 := by
  calc
    Nat.card S.augmentationPlanes ≤
        Nat.card ((o : S.OrbitBlocks) →
          S.orbitAugmentationSpace o) :=
      Nat.card_le_card_of_injective S.augmentationOrbitRestriction
        S.augmentationOrbitRestriction_injective
    _ = ∏ o : S.OrbitBlocks,
        Nat.card (S.orbitAugmentationSpace o) :=
      Nat.card_pi
    _ = ∏ _o : S.OrbitBlocks, 4 := by
      apply Finset.prod_congr rfl
      intro o _
      exact S.orbitAugmentation_card_eq_four o
    _ = 4 ^ Nat.card S.OrbitBlocks := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_eq_nat_card]
    _ = 256 := by rw [S.orbitBlocks_card]; norm_num

/-- The actual correlated averaging subgroup injects into the literal sum
of the four augmentation planes.  No equality with the full literal module
is asserted: all correlations in the original pair kernel are preserved. -/
theorem averagingSubgroup_card_le_augmentationPlanes
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p) :
    Nat.card (S.averagingSubgroup R) ≤ Nat.card S.augmentationPlanes := by
  let W := (S.averagingCoordinateRepresentation R).toSubmodule
  have hW : W ≤ R.frame.kernelSpace := fun _ hv ↦ hv.2
  have hcard : Nat.card (S.averagingSubgroup R) = Nat.card W :=
    R.frame.coordinateSubgroup_card W hW
  rw [hcard]
  exact Nat.card_le_card_of_injective
    (fun v : W ↦ ⟨v.1, v.2.1⟩)
    (by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z : S.augmentationPlanes => z.1) h)

/-- Passing to a retained quotient cannot increase the cardinality of the
four-plane image. -/
theorem retainedAveragingImage_card_le_augmentationPlanes
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : {N : Subgroup (preE7PairAction 12 p) // N.Normal}) :
    Nat.card (S.retainedAveragingImage R N) ≤
      Nat.card S.augmentationPlanes := by
  exact (Nat.card_le_card_of_surjective
    ((QuotientGroup.mk' N.1).subgroupMap (S.averagingSubgroup R))
    (MonoidHom.subgroupMap_surjective _ _)).trans
      (S.averagingSubgroup_card_le_augmentationPlanes R)

theorem retainedAveragingImage_card_le_256
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : {N : Subgroup (preE7PairAction 12 p) // N.Normal}) :
    Nat.card (S.retainedAveragingImage R N) ≤ 256 :=
  (S.retainedAveragingImage_card_le_augmentationPlanes R N).trans
    S.augmentationPlanes_card_le

/-- A faithful action of an elementary abelian ternary group of order at
least nine on a binary vector space needs at least four binary dimensions.

This is the small linear-group calculation used by every one of the eight
four-ternary rows.  It is stated without reference to the permutation
realization so that the retained-section argument only has to construct the
faithful representation. -/
theorem sixteen_le_card_of_nine_le_exponent_three_faithful_representation
    {K W : Type} [Group K] [Finite K]
    [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] [Finite W]
    (hcomm : IsMulCommutative K)
    (hexponent : ∀ k : K, k ^ (3 : ℕ) = 1)
    (hnine : 9 ≤ Nat.card K)
    (ρ : Representation (ZMod 2) K W)
    (hfaithful : Function.Injective ρ) :
    16 ≤ Nat.card W := by
  let d := Module.finrank (ZMod 2) W
  have hWcard : Nat.card W = 2 ^ d := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  letI : Finite (Module.End (ZMod 2) W) :=
    Finite.of_injective
      (fun u : Module.End (ZMod 2) W ↦ (u : W → W))
      LinearMap.coe_injective
  have hKdvdGL : Nat.card K ∣ Nat.card (Module.End (ZMod 2) W)ˣ := by
    exact Subgroup.card_dvd_of_injective ρ.toHomUnits (by
      intro x y hxy
      apply hfaithful
      exact congrArg Units.val hxy)
  letI : AddCommGroup (Additive K) :=
    { (inferInstance : AddGroup (Additive K)) with
      add_comm := fun x y => by
        apply Additive.toMul.injective
        exact (isMulCommutative_iff.mp hcomm) x.toMul y.toMul }
  letI : Module (ZMod 3) (Additive K) :=
    AddCommGroup.zmodModule (n := 3) (fun x => by
      apply Additive.toMul.injective
      change x.toMul ^ (3 : ℕ) = 1
      exact hexponent x.toMul)
  letI : Module.Finite (ZMod 3) (Additive K) := Module.Finite.of_finite
  let e := Module.finrank (ZMod 3) (Additive K)
  have hKcard : Nat.card K = 3 ^ e := by
    change Nat.card (Additive K) = 3 ^ e
    simpa only [e, Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := ZMod 3) (V := Additive K))
  have he : 2 ≤ e := by
    by_contra hnot
    have he' : e ≤ 1 := by omega
    have hpow : 3 ^ e ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) he'
    rw [← hKcard] at hpow
    omega
  have hnine_dvd_K : 9 ∣ Nat.card K := by
    rw [hKcard, show 9 = 3 ^ (2 : ℕ) by norm_num]
    exact Nat.pow_dvd_pow 3 he
  have hnine_dvd_GL : 9 ∣ Nat.card (Module.End (ZMod 2) W)ˣ :=
    hnine_dvd_K.trans hKdvdGL
  by_contra hsmall
  have hd : d ≤ 3 := by
    by_contra hnot
    have hfour : 4 ≤ d := by omega
    have hpow : 2 ^ 4 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hfour
    rw [← hWcard] at hpow
    omega
  let basis : Module.Basis
      (Fin (Module.finrank (ZMod 2) W)) (ZMod 2) W :=
    Module.finBasisOfFinrankEq (ZMod 2) W rfl
  have hGL : Nat.card (Module.End (ZMod 2) W)ˣ ∈ ({1, 6, 168} : Set ℕ) := by
    rw [← Nat.card_congr
      (Matrix.GeneralLinearGroup.toLin' basis).toEquiv,
      Matrix.card_GL_field]
    simp only [ZMod.card]
    have hcases : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
    rcases hcases with hzero | hone | htwo | hthree
    · have hdim : Module.finrank (ZMod 2) W = 0 := by simpa [d] using hzero
      rw [hdim]
      norm_num
    · have hdim : Module.finrank (ZMod 2) W = 1 := by simpa [d] using hone
      rw [hdim]
      norm_num
    · have hdim : Module.finrank (ZMod 2) W = 2 := by simpa [d] using htwo
      rw [hdim]
      norm_num
    · have hdim : Module.finrank (ZMod 2) W = 3 := by simpa [d] using hthree
      rw [hdim]
      norm_num [Fin.prod_univ_succ]
  rcases hGL with hGL | hGL | hGL
  all_goals rw [hGL] at hnine_dvd_GL <;> norm_num at hnine_dvd_GL

/-- Cardinal endpoint for the active four-plane argument.  The two
representation-theoretic premises are deliberately stated only for ambient
minimal normal factors; the conclusion then follows from the generic socle
cardinality theorem, with `16^2 = 256`. -/
theorem retainedActiveSocle_normalGen_le_two_of_fourPlaneBounds
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : {N : Subgroup (preE7PairAction 12 p) // N.Normal})
    (hsection : ∀ M : Subgroup (preE7PairAction 12 p ⧸ N.1),
      IsMinimalNormalSubgroup M →
        (⁅S.retainedTernaryImage R N, M⁆ = M ↔
          M ≤ S.retainedAveragingImage R N))
    (hmin : ∀ M : Subgroup (preE7PairAction 12 p ⧸ N.1),
      IsMinimalNormalSubgroup M →
      M ≤ S.retainedAveragingImage R N → 16 ≤ Nat.card M)
    (hcard : Nat.card (S.retainedAveragingImage R N) ≤ 256) :
    MarkedC4.normalGen
      (nontrivialActionSoclePart (preE7PairAction 12 p ⧸ N.1)
        (S.retainedTernaryImage R N)) ≤ 2 := by
  unfold nontrivialActionSoclePart
  rw [minimalNormalSoclePart_congr
    (preE7PairAction 12 p ⧸ N.1)
    (fun M ↦ ⁅S.retainedTernaryImage R N, M⁆ = M)
    (fun M ↦ M ≤ S.retainedAveragingImage R N) hsection]
  change MarkedC4.normalGen
      (finiteGroupSoclePart (preE7PairAction 12 p ⧸ N.1)
        (S.retainedAveragingImage R N)) ≤ 2
  exact normalGen_finiteGroupSoclePart_le_of_card
    (preE7PairAction 12 p ⧸ N.1) (S.retainedAveragingImage R N)
    16 2 (by norm_num) hmin (hcard.trans_eq (by norm_num))

/-- The same endpoint with the physical `256` ceiling discharged by the
four-orbit restriction theorem above. -/
theorem retainedActiveSocle_normalGen_le_two_of_faithfulSections
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : {N : Subgroup (preE7PairAction 12 p) // N.Normal})
    (hsection : ∀ M : Subgroup (preE7PairAction 12 p ⧸ N.1),
      IsMinimalNormalSubgroup M →
        (⁅S.retainedTernaryImage R N, M⁆ = M ↔
          M ≤ S.retainedAveragingImage R N))
    (hmin : ∀ M : Subgroup (preE7PairAction 12 p ⧸ N.1),
      IsMinimalNormalSubgroup M →
      M ≤ S.retainedAveragingImage R N → 16 ≤ Nat.card M) :
    MarkedC4.normalGen
      (nontrivialActionSoclePart (preE7PairAction 12 p ⧸ N.1)
        (S.retainedTernaryImage R N)) ≤ 2 :=
  S.retainedActiveSocle_normalGen_le_two_of_fourPlaneBounds R N
    hsection hmin (S.retainedAveragingImage_card_le_256 R N)

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

end DegreeTwoFourTernaryTopStructure

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
