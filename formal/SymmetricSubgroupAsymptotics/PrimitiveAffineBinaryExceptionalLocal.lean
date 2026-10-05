import SymmetricSubgroupAsymptotics.AffineNormalGraphFibre
import SymmetricSubgroupAsymptotics.CliffordHomogeneousRestrictionInput
import SymmetricSubgroupAsymptotics.ElementaryNormalModuleGenerators
import SymmetricSubgroupAsymptotics.FiniteSocleNormalGenerators
import SymmetricSubgroupAsymptotics.IrreducibleCharacterLabels
import SymmetricSubgroupAsymptotics.NormalGeneratorTypeSharing
import SymmetricSubgroupAsymptotics.PermutationSectionNormalGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineBlockCoordinateSeparation
import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveComponentSourceAssembly
import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveSmallCatalogueCapacity
import SymmetricSubgroupAsymptotics.PrimePrimarySocleTypeSharing
import SymmetricSubgroupAsymptotics.PrimeRelativeHeadZeroAbsorption
import SymmetricSubgroupAsymptotics.SchurPGroupCapacity
import SymmetricSubgroupAsymptotics.SocleGeneratorCharacterInterval
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Maschke

/-!
# The literal socle problem in affine degrees eight and sixteen

The numerical affine-capacity exhaustion leaves the five binary cells

`(8,2), (8,4), (8,6), (16,2), (16,4)`.

This file keeps the actual block system and the actual translation
intersection.  It proves the elementary facts needed before the final
whole-socle argument:

* the translation intersection injects in the product of the literal local
  translation spaces, so its order is at most `r^s`;
* its image in every literal quotient has the same bound;
* a minimal normal subgroup of the quotient is either contained in that
  translation image or is disjoint from, and hence centralizes, it;
* the local vector-space dimensions are exactly three and four;
* on the soluble branch, the exact local complement orders divide `21` and
  `360`, by the published small-affine catalogue.

There is deliberately no certificate structure postulating a tuple of
normal generators.  The tempting stronger assertion that every minimal
normal subgroup has order at least `8` (respectively `4`) is false.  For
example, a diagonal `C7` acting on two copies of `F_2^3`, together with the
block swap, has a quotient `(E8 : C7) x C2`; its final factor is a minimal
normal subgroup of order two.  Thus the last step must use the manuscript's
same-type whole-socle argument: translation and top types share character
slots.  `socleGeneratorCharacterIntervalData_of_typeSharing` below records
the exact conclusion that this argument must deliver, without turning it
into a project assumption.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

abbrev BinaryAffineLiteralNormalAxis (G : Type) [Group G] :=
  {N : Subgroup G // N.Normal}

/-- The five binary affine cells left by the numerical exhaustion. -/
inductive BinaryAffineExceptionalShape (r s : ℕ) : Prop
  | degreeEight (hr : r = 8) (hs : s = 2 ∨ s = 4 ∨ s = 6)
  | degreeSixteen (hr : r = 16) (hs : s = 2 ∨ s = 4)

/-- The common character-slot count in the binary affine proof. -/
def binaryAffineExceptionalSlots (r s : ℕ) : ℕ :=
  if r = 8 then s else 2 * s

namespace BinaryAffineExceptionalShape

theorem slots_eq_of_degreeEight {r s : ℕ}
    (_h : BinaryAffineExceptionalShape r s) (hr : r = 8) :
    binaryAffineExceptionalSlots r s = s := by
  simp [binaryAffineExceptionalSlots, hr]

theorem slots_eq_of_degreeSixteen {r s : ℕ}
    (_h : BinaryAffineExceptionalShape r s) (hr : r = 16) :
    binaryAffineExceptionalSlots r s = 2 * s := by
  simp [binaryAffineExceptionalSlots, hr]

theorem blockCount_two_le {r s : ℕ}
    (h : BinaryAffineExceptionalShape r s) : 2 ≤ s := by
  cases h with
  | degreeEight _ hs => rcases hs with rfl | rfl | rfl <;> omega
  | degreeSixteen _ hs => rcases hs with rfl | rfl <;> omega

theorem localDegree_eq {r s : ℕ}
    (h : BinaryAffineExceptionalShape r s) : r = 8 ∨ r = 16 := by
  cases h with
  | degreeEight hr _ => exact Or.inl hr
  | degreeSixteen hr _ => exact Or.inr hr

/-- Extract the exact exceptional shape from the proved numerical exception
once the binary local degree has been identified. -/
theorem ofCapacityException_of_binaryDegree {r s : ℕ}
    (h : ImprimitiveAffineCapacityException r s)
    (hr : r = 8 ∨ r = 16) : BinaryAffineExceptionalShape r s := by
  cases h with
  | degreeTwo hr' hs => rcases hr with h8 | h16 <;> omega
  | degreeThree hr' hs => rcases hr with h8 | h16 <;> omega
  | degreeFour hr' hs => rcases hr with h8 | h16 <;> omega
  | degreeFive hr' hs => rcases hr with h8 | h16 <;> omega
  | degreeEight hr' hs => exact .degreeEight hr' hs
  | degreeNine hr' hs => rcases hr with h8 | h16 <;> omega
  | degreeSixteen hr' hs => exact .degreeSixteen hr' hs

end BinaryAffineExceptionalShape

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-! ## The literal linear block kernel -/

/-- The kernel of the literal block-top map after quotienting the actual
translation intersection. -/
abbrev binaryAffineLinearBlockKernel :
    Subgroup (preE7NonPairAction w U ⧸ E block P) :=
  ((PermutationalWreathProduct.rightHom).comp
    (quotientEmbedding block P)).ker

def binaryAffineQuotientTopMap :
    (preE7NonPairAction w U ⧸ E block P) →* block.Top :=
  PermutationalWreathProduct.rightHom.comp (quotientEmbedding block P)

/-- The quotient by translations still maps onto the literal block top. -/
theorem binaryAffineQuotientTopMap_surjective :
    Function.Surjective (binaryAffineQuotientTopMap block P) := by
  intro q
  obtain ⟨g, hg⟩ := q.2
  refine ⟨QuotientGroup.mk' (E block P) g, ?_⟩
  change (block.topMap.rangeRestrict g : block.Top) = q
  exact Subtype.ext hg

/-- Its kernel is definitionally the exact linear block kernel `K`. -/
theorem binaryAffineQuotientTopMap_ker :
    (binaryAffineQuotientTopMap block P).ker =
      binaryAffineLinearBlockKernel block P := by
  rfl

/-- One literal local-complement coordinate of the linear block kernel. -/
def binaryAffineLinearBlockKernelCoordinate (i : block.Points) :
    binaryAffineLinearBlockKernel block P →* LocalQuotient block P where
  toFun x := (quotientEmbedding block P x.1).left i
  map_one' := by simp
  map_mul' x y := by
    change (quotientEmbedding block P (x.1 * y.1)).left i =
      (quotientEmbedding block P x.1).left i *
        (quotientEmbedding block P y.1).left i
    rw [map_mul, PermutationalWreathProduct.mul_left]
    have hx : (quotientEmbedding block P x.1).right = 1 := by
      have hx' := MonoidHom.mem_ker.mp x.2
      exact hx'
    rw [hx]
    simp

/-- Surjective local compression preserves the exact-component property on
the literal quotient embedding. -/
theorem quotientEmbedding_fullComponent :
    PermutationalWreathProduct.Compression.FullComponent
      (quotientEmbedding block P) := by
  intro i d
  obtain ⟨c, hc⟩ := localMap_surjective block P d
  obtain ⟨a, hai, hac⟩ :=
    ActualBlockWreathEmbedding.fullComponent
      block.map block.map_equivariant block.base i c
  refine ⟨QuotientGroup.mk' (E block P) a, ?_, ?_⟩
  · change (ambientEmbedding block a).right • i = i
    exact hai
  · change localMap block P ((ambientEmbedding block a).left i) = d
    change localMap block P
      ((ActualBlockWreathEmbedding.embedding block.map
        block.map_equivariant block.base a).left i) = d
    rw [hac, hc]

/-- Every coordinate image of the actual linear block kernel is normal in
the exact local complement.  This is the group-theoretic fact used to turn
the published local order list into the nontrivial-coordinate alternatives
of the manuscript proof. -/
theorem binaryAffineLinearBlockKernelCoordinate_range_normal
    (i : block.Points) :
    (binaryAffineLinearBlockKernelCoordinate block P i).range.Normal := by
  constructor
  rintro x ⟨e, rfl⟩ c
  obtain ⟨a, hai, hac⟩ := quotientEmbedding_fullComponent block P i c
  let K := binaryAffineLinearBlockKernel block P
  let z : K := ⟨a * e.1 * a⁻¹,
    (inferInstance : K.Normal).conj_mem e.1 e.2 a⟩
  refine ⟨z, ?_⟩
  change (quotientEmbedding block P (a * e.1 * a⁻¹)).left i =
    c * (quotientEmbedding block P e.1).left i * c⁻¹
  rw [map_mul, map_mul, map_inv]
  have he : (quotientEmbedding block P e.1).right = 1 := by
    have he' := MonoidHom.mem_ker.mp e.2
    exact he'
  rw [PermutationalWreathProduct.conj_left_of_fixed
    (quotientEmbedding block P a) (quotientEmbedding block P e.1) i hai he,
    hac]

/-- The literal coordinates jointly separate the actual linear block
kernel.  Correlated and diagonal kernels are retained: no surjectivity of
an individual coordinate is asserted. -/
theorem binaryAffineLinearBlockKernelCoordinate_joint_injective :
    Function.Injective
      (fun k i ↦ binaryAffineLinearBlockKernelCoordinate block P i k) := by
  intro x y hxy
  apply Subtype.ext
  apply quotientEmbedding_injective block P
  apply PermutationalWreathProduct.ext
  · funext i
    exact congrFun hxy i
  · exact (MonoidHom.mem_ker.mp x.2).trans
      (MonoidHom.mem_ker.mp y.2).symm

/-- Ambient conjugation transports a linear-kernel coordinate to the
corresponding transported block. -/
theorem binaryAffineLinearBlockKernelCoordinate_conjugation
    (a : preE7NonPairAction w U ⧸ E block P)
    (k : binaryAffineLinearBlockKernel block P) (i : block.Points) :
    (binaryAffineLinearBlockKernelCoordinate block P
        ((quotientEmbedding block P a).right • i)
        (MulAut.conjNormal a k) : LocalQuotient block P) =
      (quotientEmbedding block P a).left
          ((quotientEmbedding block P a).right • i) *
        binaryAffineLinearBlockKernelCoordinate block P i k *
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

/-- The stabilizer of one literal block inside `U/E`. -/
abbrev binaryAffineQuotientTopStabilizer (i : block.Points) :
    Subgroup (preE7NonPairAction w U ⧸ E block P) :=
  (MulAction.stabilizer block.Top i).comap
    (binaryAffineQuotientTopMap block P)

/-- Local affine-complement coordinate on the actual block stabilizer. -/
def binaryAffineStabilizerComponent (i : block.Points) :
    binaryAffineQuotientTopStabilizer block P i →*
      LocalQuotient block P where
  toFun a := (quotientEmbedding block P a.1).left i
  map_one' := by simp
  map_mul' x y := by
    change (quotientEmbedding block P (x.1 * y.1)).left i =
      (quotientEmbedding block P x.1).left i *
        (quotientEmbedding block P y.1).left i
    rw [map_mul, PermutationalWreathProduct.mul_left]
    have hx : (quotientEmbedding block P x.1).right⁻¹ • i = i := by
      have hx₀ : (quotientEmbedding block P x.1).right • i = i := x.2
      calc
        (quotientEmbedding block P x.1).right⁻¹ • i =
            (quotientEmbedding block P x.1).right⁻¹ •
              ((quotientEmbedding block P x.1).right • i) :=
          congrArg ((quotientEmbedding block P x.1).right⁻¹ • ·) hx₀.symm
        _ = i := inv_smul_smul _ _
    simp only [Pi.mul_apply, hx]

/-- Exact-component fullness makes the stabilizer component onto. -/
theorem binaryAffineStabilizerComponent_surjective (i : block.Points) :
    Function.Surjective (binaryAffineStabilizerComponent block P i) := by
  intro c
  obtain ⟨a, hai, hac⟩ := quotientEmbedding_fullComponent block P i c
  exact ⟨⟨a, hai⟩, hac⟩

/-- Projection of the actual block stabilizer to the corresponding
stabilizer in the literal top. -/
def binaryAffineStabilizerTopMap (i : block.Points) :
    binaryAffineQuotientTopStabilizer block P i →*
      MulAction.stabilizer block.Top i where
  toFun a := ⟨binaryAffineQuotientTopMap block P a.1, a.2⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (binaryAffineQuotientTopMap block P)
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (binaryAffineQuotientTopMap block P) x.1 y.1

/-- If the actual linear block kernel vanished, the block stabilizer would
embed in the top stabilizer. -/
theorem binaryAffineStabilizerTopMap_injective_of_kernel_eq_bot
    (i : block.Points)
    (hK : binaryAffineLinearBlockKernel block P = ⊥) :
    Function.Injective (binaryAffineStabilizerTopMap block P i) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rw [eq_bot_iff]
  intro x hx
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  have hxK : x.1 ∈ binaryAffineLinearBlockKernel block P := by
    rw [← binaryAffineQuotientTopMap_ker block P]
    apply MonoidHom.mem_ker.mpr
    exact congrArg
      (fun q : MulAction.stabilizer block.Top i => (q.1 : block.Top))
      (MonoidHom.mem_ker.mp hx)
  rw [hK] at hxK
  exact Subgroup.mem_bot.mp hxK

/-- The cardinality of a point stabilizer in the literal transitive top
divides `(s-1)!`. -/
theorem binaryAffineTopStabilizer_card_dvd_factorial_pred
    (i : block.Points) :
    Nat.card (MulAction.stabilizer block.Top i) ∣
      (Nat.card block.Points - 1).factorial := by
  letI : MulAction.IsPretransitive block.Top block.Points :=
    block.top_pretransitive
  letI : Finite block.Top := block.top_finite
  have htop : Nat.card block.Top ∣ (Nat.card block.Points).factorial := by
    have h := Subgroup.card_dvd_of_injective block.Top.subtype
      (show Function.Injective block.Top.subtype from Subtype.val_injective)
    simpa only [Nat.card_eq_fintype_card, Fintype.card_perm] using h
  have hindex : (MulAction.stabilizer block.Top i).index =
      Nat.card block.Points := by
    simpa only [Fintype.card_eq_nat_card] using
      MulAction.index_stabilizer_of_transitive block.Top i
  have hmul := (MulAction.stabilizer block.Top i).card_mul_index
  rw [hindex] at hmul
  have hpoints : 0 < Nat.card block.Points := by
    simpa only [Nat.card_eq_fintype_card] using
      (Fintype.card_pos_iff.mpr ⟨i⟩)
  obtain ⟨n, hn : Nat.card block.Points = n + 1⟩ :=
    Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt hpoints)
  rw [hn] at hmul htop ⊢
  simp only [Nat.add_sub_cancel]
  obtain ⟨c, hc⟩ := htop
  refine ⟨c, ?_⟩
  apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < n + 1)
  symm
  calc
    (n + 1) *
        (Nat.card (MulAction.stabilizer block.Top i) * c) =
      (Nat.card (MulAction.stabilizer block.Top i) * (n + 1)) * c := by
        ac_rfl
    _ = Nat.card block.Top * c := by rw [hmul]
    _ = (n + 1).factorial := hc.symm
    _ = (n + 1) * n.factorial := Nat.factorial_succ n

/-- Vanishing of one coordinate range forces vanishing of the whole actual
linear block kernel.  This uses transitivity of the retained literal top
and the exact conjugation formula; it does not enlarge the kernel to a
product. -/
theorem binaryAffineLinearBlockKernel_eq_bot_of_coordinate_range_eq_bot
    (i₀ : block.Points)
    (hzero : (binaryAffineLinearBlockKernelCoordinate block P i₀).range =
      ⊥) :
    binaryAffineLinearBlockKernel block P = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  apply Subgroup.mem_bot.mpr
  let k : binaryAffineLinearBlockKernel block P := ⟨x, hx⟩
  have hkone : k = 1 := by
    apply binaryAffineLinearBlockKernelCoordinate_joint_injective block P
    funext i
    letI : MulAction.IsPretransitive block.Top block.Points :=
      block.top_pretransitive
    obtain ⟨q, hq⟩ := MulAction.exists_smul_eq block.Top i₀ i
    obtain ⟨a, ha⟩ := binaryAffineQuotientTopMap_surjective block P q
    let k₀ : binaryAffineLinearBlockKernel block P :=
      MulAut.conjNormal a⁻¹ k
    have hk₀ : binaryAffineLinearBlockKernelCoordinate block P i₀ k₀ =
        1 := by
      apply Subtype.ext
      have hmem : binaryAffineLinearBlockKernelCoordinate block P i₀ k₀ ∈
          (binaryAffineLinearBlockKernelCoordinate block P i₀).range :=
        ⟨k₀, rfl⟩
      rw [hzero] at hmem
      exact congrArg Subtype.val (Subgroup.mem_bot.mp hmem)
    have hconj :=
      binaryAffineLinearBlockKernelCoordinate_conjugation block P a k₀ i₀
    have htop : (quotientEmbedding block P a).right • i₀ = i := by
      change binaryAffineQuotientTopMap block P a • i₀ = i
      rw [ha]
      exact hq
    have hkconj : MulAut.conjNormal a k₀ = k := by
      apply Subtype.ext
      simp [k₀]
    rw [htop, hkconj, hk₀, mul_one, mul_inv_cancel] at hconj
    simpa only [map_one] using hconj
  exact congrArg Subtype.val hkone

/-! ## The exact local linear representation -/

/-- The faithful range compression identifies the literal affine complement
with `LocalQuotient`; this is an isomorphism of the actual groups, not a
catalogue replacement. -/
noncomputable def binaryAffineLocalComplementEquiv :
    P.complement (origin block) ≃* LocalQuotient block P :=
  MulEquiv.ofBijective (complementAction block P).rangeRestrict
    ⟨MonoidHom.rangeRestrict_injective_iff.mpr
        (complementAction_injective block P),
      (complementAction block P).rangeRestrict_surjective⟩

/-- The compressed local group is exactly the literal affine complement,
not merely a group of the same bounded order. -/
theorem localQuotient_card_eq_complement :
    Nat.card (LocalQuotient block P) =
      Nat.card (P.complement (origin block)) := by
  exact Nat.card_congr (binaryAffineLocalComplementEquiv block P).symm.toEquiv

/-- The exact local complement acting on its literal affine translation
module, transported only across the preceding range equivalence. -/
noncomputable abbrev binaryAffineLocalLinearRepresentation :
    Rep (ZMod P.p) (LocalQuotient block P) := by
  let C := chart block P
  letI : Fact P.p.Prime := C.primeFact
  exact Rep.of ((P.complementRepresentation
    (primitive block) C (origin block)).ρ.comp
      (binaryAffineLocalComplementEquiv block P).symm.toMonoidHom)

/-- The transported local linear representation remains faithful. -/
theorem binaryAffineLocalLinearRepresentation_injective :
    let C := chart block P
    letI : Fact P.p.Prime := C.primeFact
    Function.Injective
      (binaryAffineLocalLinearRepresentation block P).ρ := by
  let C := chart block P
  letI : Fact P.p.Prime := C.primeFact
  exact (P.complementRepresentation_injective
    (primitive block) C (origin block)).comp
      (binaryAffineLocalComplementEquiv block P).symm.injective

/-- The transported local linear representation remains irreducible. -/
theorem binaryAffineLocalLinearRepresentation_irreducible :
    let C := chart block P
    letI : Fact P.p.Prime := C.primeFact
    Representation.IsIrreducible
      (binaryAffineLocalLinearRepresentation block P).ρ := by
  let C := chart block P
  letI : Fact P.p.Prime := C.primeFact
  letI : Representation.IsIrreducible
      (P.complementRepresentation
        (primitive block) C (origin block)).ρ :=
    P.complementRepresentation_irreducible
      (primitive block) C (origin block)
  exact representation_irreducible_comp
    (P.complementRepresentation
      (primitive block) C (origin block)).ρ
    (binaryAffineLocalComplementEquiv block P).symm.toMonoidHom
    (binaryAffineLocalComplementEquiv block P).symm.surjective

set_option maxHeartbeats 800000 in
/-- The generic actual-wreath local representation used by the published
Clifford input is the same literal conjugation representation as the affine
complement representation above.  This comparison is made through the
canonical quotients of the same local map; no abstract action of the same
order is substituted. -/
theorem cliffordLocalRepresentation_rho_eq
    (hTraceyPerm : TraceyPermutationGeneratorInput) :
    let S := initialState hTraceyPerm block
    let C := localTranslationChart block P
    (CliffordHomogeneousRestriction.localRepresentation
      S (localMap block P) (localMap_surjective block P) C).ρ =
      (binaryAffineLocalLinearRepresentation block P).ρ := by
  let S := initialState hTraceyPerm block
  let C := localTranslationChart block P
  let ε := CliffordHomogeneousRestriction.localQuotientEquiv
    S (localMap block P) (localMap_surjective block P)
  let δ := binaryAffineLocalComplementEquiv block P
  apply MonoidHom.ext
  intro q
  apply LinearMap.ext
  intro v
  let c : P.complement (origin block) := δ.symm q
  have hcq : complementAction block P c = q := by
    exact congrArg Subtype.val (δ.apply_symm_apply q)
  have hlocal : localMap block P c.1 = q := by
    apply Subtype.ext
    simpa only [localMap, MonoidHom.comp_apply,
      P.complementProjection_complement] using hcq
  have hclass : ε.symm q =
      QuotientGroup.mk' (localMap block P).ker c.1 := by
    apply ε.injective
    rw [ε.apply_symm_apply]
    exact hlocal.symm
  let e : (localMap block P).ker :=
    localKernelEquiv block P (Multiplicative.ofAdd v)
  have he : C.equiv e = Multiplicative.ofAdd v := by
    change (localKernelEquiv block P).symm
      (localKernelEquiv block P (Multiplicative.ofAdd v)) = _
    exact (localKernelEquiv block P).symm_apply_apply
      (Multiplicative.ofAdd v)
  change C.quotientRepresentation.ρ (ε.symm q) v =
    (P.complementRepresentation
      (primitive block) (chart block P) (origin block)).ρ c v
  rw [hclass]
  apply Multiplicative.ofAdd.injective
  change Multiplicative.ofAdd
      (C.quotientRepresentation.ρ
        (QuotientGroup.mk' (localMap block P).ker c.1) v) =
    Multiplicative.ofAdd
      ((P.complementRepresentation
        (primitive block) (chart block P) (origin block)).ρ c v)
  have hev : (C.equiv e).toAdd = v :=
    congrArg Multiplicative.toAdd he
  conv_lhs =>
    rw [← hev, C.quotientRepresentation_apply]
  change C.equiv (MulAut.conjNormal c.1 e) = _
  rw [P.complementRepresentation_apply]
  simp only [ofAdd_toAdd]
  apply (localKernelEquiv block P).injective
  apply Subtype.ext
  rw [show C.equiv (MulAut.conjNormal c.1 e) =
      (localKernelEquiv block P).symm (MulAut.conjNormal c.1 e) by rfl,
    (localKernelEquiv block P).apply_symm_apply]
  change c.1 * e.1 * c.1⁻¹ =
    (((P.bottomKernelEquiv (primitive block) (chart block P) (origin block))
      ((chart block P).equiv
        (P.complementAction (origin block) c
          ((chart block P).equiv.symm (Multiplicative.ofAdd v)))) :
        (P.complementProjection (origin block)).ker) : block.Component)
  rw [P.bottomKernelEquiv_coe,
    (chart block P).equiv.symm_apply_apply]
  rw [show (e.1 : block.Component) =
      ((chart block P).equiv.symm (Multiplicative.ofAdd v) : P.V) by rfl]
  rfl

/-- A nontrivial normal local subgroup has no fixed vector on the literal
irreducible affine translation module.  Normality makes its fixed space
invariant under the entire exact local complement; irreducibility and
faithfulness then rule out both nonzero alternatives. -/
theorem binaryAffineLocalNormal_invariants_eq_bot
    (D : Subgroup (LocalQuotient block P)) [D.Normal]
    (hD : D ≠ ⊥) :
    let C := chart block P
    letI : Fact P.p.Prime := C.primeFact
    Representation.invariants
      ((binaryAffineLocalLinearRepresentation block P).ρ.comp D.subtype) =
        ⊥ := by
  let C := chart block P
  letI : Fact P.p.Prime := C.primeFact
  let ρ := (binaryAffineLocalLinearRepresentation block P).ρ
  let W : Subrepresentation ρ :=
    { toSubmodule := Representation.invariants (ρ.comp D.subtype)
      apply_mem_toSubmodule := by
        intro g v hv
        exact Representation.le_comap_invariants ρ D g hv }
  letI : Representation.IsIrreducible ρ :=
    binaryAffineLocalLinearRepresentation_irreducible block P
  rcases (inferInstance : Representation.IsIrreducible ρ)
      |>.eq_bot_or_eq_top W with hbot | htop
  · exact congrArg Subrepresentation.toSubmodule hbot
  · exfalso
    apply hD
    rw [eq_bot_iff]
    intro d hd
    apply Subgroup.mem_bot.mpr
    have hρd : ρ d = 1 := by
      ext v
      have hvW : v ∈ W := by rw [htop]; exact Submodule.mem_top
      exact hvW ⟨d, hd⟩
    exact (binaryAffineLocalLinearRepresentation_injective block P)
      (hρd.trans (map_one ρ).symm)

/-- The image of the literal translation intersection in a retained normal
quotient. -/
abbrev binaryAffineTranslationImage
    (N : BinaryAffineLiteralNormalAxis (preE7NonPairAction w U)) :
    Subgroup (preE7NonPairAction w U ⧸ N.1) :=
  (E block P).map (QuotientGroup.mk' N.1)

/-- The actual translation intersection embeds in the product of the
literal local translation spaces. -/
theorem translationIntersection_card_le :
    Nat.card (E block P) ≤
      Nat.card block.Fibre ^ Nat.card block.Points := by
  have hV : Nat.card (chart block P).V = Nat.card block.Fibre := by
    calc
      Nat.card (chart block P).V =
          Nat.card (Multiplicative (chart block P).V) := rfl
      _ = Nat.card P.V := Nat.card_congr (chart block P).equiv.symm.toEquiv
      _ = Nat.card block.Fibre := P.card_eq (origin block)
  letI : Finite (chart block P).V := Finite.of_injective
    (fun v : (chart block P).V =>
      (chart block P).equiv.symm (Multiplicative.ofAdd v))
    (chart block P).equiv.symm.injective
  calc
    Nat.card (E block P) ≤
        Nat.card (Multiplicative
          (block.Points → (chart block P).V)) :=
      Nat.card_le_card_of_injective (coordinates block P)
        (coordinates_injective block P)
    _ = Nat.card (block.Points → (chart block P).V) := rfl
    _ = Nat.card (chart block P).V ^ Nat.card block.Points := by
      rw [Nat.card_fun]
    _ = Nat.card block.Fibre ^ Nat.card block.Points := by rw [hV]

/-- Passing to a literal normal quotient cannot enlarge the actual
translation intersection. -/
theorem translationImage_card_le_translationIntersection
    (N : BinaryAffineLiteralNormalAxis (preE7NonPairAction w U)) :
    Nat.card (binaryAffineTranslationImage block P N) ≤
      Nat.card (E block P) := by
  exact Nat.card_le_card_of_surjective
    ((QuotientGroup.mk' N.1).subgroupMap (E block P))
    (MonoidHom.subgroupMap_surjective _ _)

/-- The quotient translation image has the exact coordinate-product upper
bound retained from the actual block system. -/
theorem translationImage_card_le_coordinateProduct
    (N : BinaryAffineLiteralNormalAxis (preE7NonPairAction w U)) :
    Nat.card (binaryAffineTranslationImage block P N) ≤
      Nat.card block.Fibre ^ Nat.card block.Points :=
  (translationImage_card_le_translationIntersection block P N).trans
    (translationIntersection_card_le block P)

/-- The elementary translation space in local degree eight is binary of
dimension three. -/
theorem degreeEight_translationDimension
    (hr : Nat.card block.Fibre = 8) :
    P.p = 2 ∧ (chart block P).d = 3 := by
  let C := chart block P
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v))
    C.equiv.symm.injective
  have hdegree : 8 = P.p ^ C.d := by
    rw [← hr]
    simpa [PrimitiveAffineProfile.ElementaryChart.d] using
      P.degree_eq_prime_pow_finrank C.equiv (origin block)
  exact prime_pow_positive_injective (d := C.d) (e := 3)
    P.p_prime Nat.prime_two C.d_pos (by norm_num)
      (hdegree.symm.trans (by norm_num))

/-- The elementary translation space in local degree sixteen is binary of
dimension four. -/
theorem degreeSixteen_translationDimension
    (hr : Nat.card block.Fibre = 16) :
    P.p = 2 ∧ (chart block P).d = 4 := by
  let C := chart block P
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v))
    C.equiv.symm.injective
  have hdegree : 16 = P.p ^ C.d := by
    rw [← hr]
    simpa [PrimitiveAffineProfile.ElementaryChart.d] using
      P.degree_eq_prime_pow_finrank C.equiv (origin block)
  exact prime_pow_positive_injective (d := C.d) (e := 4)
    P.p_prime Nat.prime_two C.d_pos (by norm_num)
      (hdegree.symm.trans (by norm_num))

private theorem degreeEight_seven_dvd_of_solubleRow
    (r : SmallAffineCatalogueRow) (hd : r.degree = 8)
    (hs : r.nonsoluble = false) : 7 ∣ r.complementOrder := by
  rcases r with ⟨i⟩ | ⟨i⟩ | ⟨i⟩ <;>
    fin_cases i <;>
    simp_all [SmallAffineCatalogueRow.degree,
      SmallAffineCatalogueRow.complementOrder,
      SmallAffineCatalogueRow.nonsoluble]

private theorem degreeSixteen_not_dvd_six_of_solubleRow
    (r : SmallAffineCatalogueRow) (hd : r.degree = 16)
    (hs : r.nonsoluble = false) : ¬ r.complementOrder ∣ 6 := by
  rcases r with ⟨i⟩ | ⟨i⟩ | ⟨i⟩ <;>
    fin_cases i <;>
    simp_all [SmallAffineCatalogueRow.degree,
      SmallAffineCatalogueRow.complementOrder,
      SmallAffineCatalogueRow.nonsoluble]

/-- Locate the literal soluble complement in the exact published row.  The
row, its degree, and its exact order are all retained. -/
theorem binaryAffineExceptional_locate_soluble_complement
    (published : PublishedPrimitiveAffineSmallCatalogueData)
    (shape : BinaryAffineExceptionalShape
      (Nat.card block.Fibre) (Nat.card block.Points))
    (hsoluble : IsSolvable (P.complement (origin block))) :
    ∃ r : SmallAffineCatalogueRow,
      r.degree = Nat.card block.Fibre ∧ r.nonsoluble = false ∧
      Nat.card (P.complement (origin block)) = r.complementOrder := by
  apply PrimitiveAffineSmallCatalogueBridge.locate_soluble
    published.locator published.representativeFacts
      block.component_preprimitive P (origin block)
  · rcases shape.localDegree_eq with h8 | h16
    · exact Or.inl h8
    · exact Or.inr (Or.inl h16)
  · exact hsoluble

/-- The exact divisibility obstruction used to prove that the local linear
kernel has nontrivial coordinate image: in degree eight the complement has
a factor seven, while in soluble degree sixteen it cannot be a quotient of
a subgroup of `S3`. -/
theorem binaryAffineExceptional_local_order_obstruction
    (published : PublishedPrimitiveAffineSmallCatalogueData)
    (shape : BinaryAffineExceptionalShape
      (Nat.card block.Fibre) (Nat.card block.Points))
    (hsoluble : IsSolvable (P.complement (origin block))) :
    (Nat.card block.Fibre = 8 ∧
        7 ∣ Nat.card (P.complement (origin block))) ∨
      (Nat.card block.Fibre = 16 ∧
        ¬ Nat.card (P.complement (origin block)) ∣ 6) := by
  obtain ⟨r, hrDegree, hrSoluble, hrOrder⟩ :=
    binaryAffineExceptional_locate_soluble_complement
      block P published shape hsoluble
  cases shape with
  | degreeEight hr _hs =>
    left
    refine ⟨hr, ?_⟩
    rw [hrOrder]
    exact degreeEight_seven_dvd_of_solubleRow r
      (hrDegree.trans hr) hrSoluble
  | degreeSixteen hr _hs =>
    right
    refine ⟨hr, ?_⟩
    rw [hrOrder]
    exact degreeSixteen_not_dvd_six_of_solubleRow r
      (hrDegree.trans hr) hrSoluble

/-- In every soluble degree-eight or degree-sixteen exceptional cell, each
coordinate image of the actual linear block kernel is nonzero.  If one
coordinate vanished, transitivity and conjugation would kill the whole
kernel.  Exact-component fullness would then make the local complement a
section of a point stabilizer in the top; the published local orders rule
this out at the five literal block counts. -/
theorem binaryAffineLinearBlockKernelCoordinate_range_ne_bot
    (published : PublishedPrimitiveAffineSmallCatalogueData)
    (shape : BinaryAffineExceptionalShape
      (Nat.card block.Fibre) (Nat.card block.Points))
    (hsoluble : IsSolvable (P.complement (origin block)))
    (i : block.Points) :
    (binaryAffineLinearBlockKernelCoordinate block P i).range ≠ ⊥ := by
  intro hzero
  have hK : binaryAffineLinearBlockKernel block P = ⊥ :=
    binaryAffineLinearBlockKernel_eq_bot_of_coordinate_range_eq_bot
      block P i hzero
  have hlocal_stabilizer : Nat.card (LocalQuotient block P) ∣
      Nat.card (binaryAffineQuotientTopStabilizer block P i) :=
    Subgroup.card_dvd_of_surjective
      (binaryAffineStabilizerComponent block P i)
      (binaryAffineStabilizerComponent_surjective block P i)
  have hstabilizer_top :
      Nat.card (binaryAffineQuotientTopStabilizer block P i) ∣
        Nat.card (MulAction.stabilizer block.Top i) :=
    Subgroup.card_dvd_of_injective
      (binaryAffineStabilizerTopMap block P i)
      (binaryAffineStabilizerTopMap_injective_of_kernel_eq_bot
        block P i hK)
  have hlocal_factorial : Nat.card (LocalQuotient block P) ∣
      (Nat.card block.Points - 1).factorial :=
    hlocal_stabilizer.trans (hstabilizer_top.trans
      (binaryAffineTopStabilizer_card_dvd_factorial_pred block i))
  have hlocalCard : Nat.card (LocalQuotient block P) =
      Nat.card (P.complement (origin block)) :=
    localQuotient_card_eq_complement block P
  rcases binaryAffineExceptional_local_order_obstruction
      block P published shape hsoluble with h8 | h16
  · have h7 : 7 ∣ Nat.card (LocalQuotient block P) := by
      rw [hlocalCard]
      exact h8.2
    have hbad : 7 ∣ (Nat.card block.Points - 1).factorial :=
      h7.trans hlocal_factorial
    cases shape with
    | degreeEight _ hs =>
      rcases hs with hs | hs | hs <;> rw [hs] at hbad <;> norm_num at hbad
    | degreeSixteen hr _ => exact (by omega)
  · have hnot : ¬ Nat.card (LocalQuotient block P) ∣ 6 := by
      rw [hlocalCard]
      exact h16.2
    apply hnot
    refine hlocal_factorial.trans ?_
    cases shape with
    | degreeEight hr _ => exact (by omega)
    | degreeSixteen _ hs =>
      rcases hs with hs | hs <;> rw [hs] <;> norm_num

/-- The published Clifford input now yields the exact faithful-core-section
dichotomy on the literal retained quotient.  The statement is the one used
by the action-type socle split above; no affine conclusion is included in
the literature input itself. -/
theorem binaryAffineExceptional_complement_order_divisor
    (published : PublishedPrimitiveAffineSmallCatalogueData)
    (shape : BinaryAffineExceptionalShape
      (Nat.card block.Fibre) (Nat.card block.Points))
    (hsoluble : IsSolvable (P.complement (origin block))) :
    (Nat.card block.Fibre = 8 ∧
        Nat.card (P.complement (origin block)) ∣ 21) ∨
      (Nat.card block.Fibre = 16 ∧
        Nat.card (P.complement (origin block)) ∣ 360) := by
  cases shape with
  | degreeEight hr _hs =>
    exact Or.inl ⟨hr,
      PrimitiveAffineSmallCatalogueBridge.degreeEight_soluble_card_dvd_twentyOne
        published.locator published.representativeFacts
        block.component_preprimitive P (origin block) hr hsoluble⟩
  | degreeSixteen hr _hs =>
    exact Or.inr ⟨hr,
      PrimitiveAffineSmallCatalogueBridge.degreeSixteen_soluble_card_dvd_threeSixty
        published.locator published.representativeFacts
        block.component_preprimitive P (origin block) hr hsoluble⟩

/-- In soluble local degree eight, every nonzero normal coordinate image of
the actual linear block kernel has order divisible by seven.  Its order
divides `21`; order three is impossible because a three-group acting on the
eight-element local translation space has more than the zero fixed vector,
contradicting local irreducibility and faithfulness. -/
theorem degreeEight_seven_dvd_coordinate_range_card
    (published : PublishedPrimitiveAffineSmallCatalogueData)
    (shape : BinaryAffineExceptionalShape
      (Nat.card block.Fibre) (Nat.card block.Points))
    (hr : Nat.card block.Fibre = 8)
    (hsoluble : IsSolvable (P.complement (origin block)))
    (i : block.Points) :
    7 ∣ Nat.card
      (binaryAffineLinearBlockKernelCoordinate block P i).range := by
  let D := (binaryAffineLinearBlockKernelCoordinate block P i).range
  letI : D.Normal :=
    binaryAffineLinearBlockKernelCoordinate_range_normal block P i
  have hDne : D ≠ ⊥ :=
    binaryAffineLinearBlockKernelCoordinate_range_ne_bot
      block P published shape hsoluble i
  have hlocal : Nat.card (LocalQuotient block P) ∣ 21 := by
    rw [localQuotient_card_eq_complement block P]
    rcases binaryAffineExceptional_complement_order_divisor
      block P published shape hsoluble with h8 | h16
    · exact h8.2
    · exact False.elim (by omega)
  have hDdiv : Nat.card D ∣ 21 :=
    (Subgroup.card_dvd_of_injective D.subtype Subtype.val_injective).trans
      hlocal
  by_contra h7
  have hcop : Nat.Coprime (Nat.card D) 7 :=
    (((show Nat.Prime 7 by norm_num).coprime_iff_not_dvd).2 h7).symm
  have hDdiv3 : Nat.card D ∣ 3 := by
    exact hcop.dvd_mul_right.mp (by simpa only [show 21 = 3 * 7 by norm_num]
      using hDdiv)
  have hDone : Nat.card D ≠ 1 := by
    intro hone
    letI : Subsingleton D := (Nat.card_eq_one_iff_unique.mp hone).1
    apply hDne
    rw [eq_bot_iff]
    intro d hd
    exact congrArg Subtype.val (Subsingleton.elim ⟨d, hd⟩ 1)
  have hDcard : Nat.card D = 3 :=
    ((Nat.dvd_prime Nat.prime_three).mp hDdiv3).resolve_left hDone
  have hDp : IsPGroup 3 D :=
    IsPGroup.of_card (n := 1) (by simpa only [pow_one] using hDcard)
  let C := chart block P
  letI : Fact P.p.Prime := C.primeFact
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v))
    C.equiv.symm.injective
  let ρD := (binaryAffineLocalLinearRepresentation block P).ρ.comp D.subtype
  letI : MulAction D C.V :=
    { smul := fun d v => ρD d v
      one_smul := by intro v; change ρD 1 v = v; simp
      mul_smul := by
        intro a b v
        change ρD (a * b) v = ρD a (ρD b v)
        rw [map_mul]
        rfl }
  have hfixedCard : Nat.card (MulAction.fixedPoints D C.V) = 1 := by
    apply Nat.card_eq_one_iff_unique.mpr
    refine ⟨?_, ⟨⟨0, by intro d; exact map_zero (ρD d)⟩⟩⟩
    constructor
    intro x y
    apply Subtype.ext
    have hxInv : x.1 ∈ Representation.invariants ρD := x.2
    have hyInv : y.1 ∈ Representation.invariants ρD := y.2
    rw [binaryAffineLocalNormal_invariants_eq_bot block P D hDne] at hxInv
    rw [binaryAffineLocalNormal_invariants_eq_bot block P D hDne] at hyInv
    rw [(Submodule.mem_bot (R := ZMod P.p)).mp hxInv,
      (Submodule.mem_bot (R := ZMod P.p)).mp hyInv]
  have hVcard : Nat.card C.V = 8 := by
    calc
      Nat.card C.V = Nat.card (Multiplicative C.V) := rfl
      _ = Nat.card P.V := Nat.card_congr C.equiv.symm.toEquiv
      _ = Nat.card block.Fibre := P.card_eq (origin block)
      _ = 8 := hr
  have hmod := hDp.card_modEq_card_fixedPoints C.V
  rw [hVcard, hfixedCard] at hmod
  exact (by norm_num : ¬ (8 ≡ 1 [MOD 3])) hmod

/-- Consequently the literal correlated linear block kernel itself has
order divisible by seven. -/
theorem degreeEight_seven_dvd_linearBlockKernel_card
    (published : PublishedPrimitiveAffineSmallCatalogueData)
    (shape : BinaryAffineExceptionalShape
      (Nat.card block.Fibre) (Nat.card block.Points))
    (hr : Nat.card block.Fibre = 8)
    (hsoluble : IsSolvable (P.complement (origin block)))
    (i : block.Points) :
    7 ∣ Nat.card (binaryAffineLinearBlockKernel block P) := by
  exact (degreeEight_seven_dvd_coordinate_range_card
    block P published shape hr hsoluble i).trans
      (Subgroup.card_dvd_of_surjective
        (binaryAffineLinearBlockKernelCoordinate block P i).rangeRestrict
        (binaryAffineLinearBlockKernelCoordinate block P i).rangeRestrict_surjective)

/-! The remaining dimension arguments are deliberately separated from the
dependent Clifford plumbing.  This keeps normalization of the literal
retained constituent out of the finite general-linear-group calculation. -/

/-- A faithful binary representation of a finite group whose order is
divisible by seven has dimension at least three. -/
private theorem eight_le_card_of_seven_dvd_faithful_representation
    {p : ℕ} [Fact p.Prime]
    {K W : Type} [Group K] [Finite K]
    [AddCommGroup W] [Module (ZMod p) W]
    [FiniteDimensional (ZMod p) W] [Finite W]
    (hp : p = 2) (ρ : Representation (ZMod p) K W)
    (hfaithful : Function.Injective ρ)
    (hseven : 7 ∣ Nat.card K) :
    8 ≤ Nat.card W := by
  subst p
  let d := Module.finrank (ZMod 2) W
  have hWcard : Nat.card W = 2 ^ d := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  letI : Finite (Module.End (ZMod 2) W) :=
    Finite.of_injective
      (fun u : Module.End (ZMod 2) W => (u : W → W))
      LinearMap.coe_injective
  have hKleGL : Nat.card K ≤ Nat.card (Module.End (ZMod 2) W)ˣ := by
    exact Nat.card_le_card_of_injective ρ.toHomUnits (by
      intro x y hxy
      apply hfaithful
      exact congrArg Units.val hxy)
  have hsevenK : 7 ≤ Nat.card K :=
    Nat.le_of_dvd (Nat.card_pos (α := K)) hseven
  by_contra hsmall
  have hd : d ≤ 2 := by
    by_contra hnot
    have hthree : 3 ≤ d := by omega
    have hpow : 2 ^ 3 ≤ 2 ^ d :=
      Nat.pow_le_pow_right (by norm_num) hthree
    rw [← hWcard] at hpow
    omega
  have hGLle : Nat.card (Module.End (ZMod 2) W)ˣ ≤ 6 := by
    let basis : Module.Basis
        (Fin (Module.finrank (ZMod 2) W)) (ZMod 2) W :=
      Module.finBasisOfFinrankEq (ZMod 2) W rfl
    rw [← Nat.card_congr
      (Matrix.GeneralLinearGroup.toLin' basis).toEquiv,
      Matrix.card_GL_field]
    simp only [ZMod.card]
    have hcases : d = 0 ∨ d = 1 ∨ d = 2 := by omega
    rcases hcases with hzero | hone | htwo
    · have hdim : Module.finrank (ZMod 2) W = 0 := by simpa [d] using hzero
      rw [hdim]
      norm_num
    · have hdim : Module.finrank (ZMod 2) W = 1 := by simpa [d] using hone
      rw [hdim]
      norm_num
    · have hdim : Module.finrank (ZMod 2) W = 2 := by simpa [d] using htwo
      rw [hdim]
      norm_num
  omega

/-- A faithful nontrivial group action on a binary vector space forces that
space to have at least four elements. -/
private theorem four_le_card_of_nontrivial_faithful_representation
    {p : ℕ} [Fact p.Prime]
    {K W : Type} [Group K] [Finite K]
    [AddCommGroup W] [Module (ZMod p) W]
    [FiniteDimensional (ZMod p) W] [Finite W]
    (hp : p = 2) (ρ : Representation (ZMod p) K W)
    (hfaithful : Function.Injective ρ)
    (hK : Nat.card K ≠ 1) :
    4 ≤ Nat.card W := by
  subst p
  let d := Module.finrank (ZMod 2) W
  have hWcard : Nat.card W = 2 ^ d := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  letI : Finite (Module.End (ZMod 2) W) :=
    Finite.of_injective
      (fun u : Module.End (ZMod 2) W => (u : W → W))
      LinearMap.coe_injective
  by_contra hsmall
  have hd : d ≤ 1 := by
    by_contra hnot
    have htwo : 2 ≤ d := by omega
    have hpow : 2 ^ 2 ≤ 2 ^ d :=
      Nat.pow_le_pow_right (by norm_num) htwo
    rw [← hWcard] at hpow
    omega
  have hGLone : Nat.card (Module.End (ZMod 2) W)ˣ = 1 := by
    let basis : Module.Basis
        (Fin (Module.finrank (ZMod 2) W)) (ZMod 2) W :=
      Module.finBasisOfFinrankEq (ZMod 2) W rfl
    rw [← Nat.card_congr
      (Matrix.GeneralLinearGroup.toLin' basis).toEquiv,
      Matrix.card_GL_field]
    simp only [ZMod.card]
    have hcases : d = 0 ∨ d = 1 := by omega
    rcases hcases with hzero | hone
    · have hdim : Module.finrank (ZMod 2) W = 0 := by simpa [d] using hzero
      rw [hdim]
      norm_num
    · have hdim : Module.finrank (ZMod 2) W = 1 := by simpa [d] using hone
      rw [hdim]
      norm_num
  have hKleGL : Nat.card K ≤ Nat.card (Module.End (ZMod 2) W)ˣ := by
    exact Nat.card_le_card_of_injective ρ.toHomUnits (by
      intro x y hxy
      apply hfaithful
      exact congrArg Units.val hxy)
  rw [hGLone] at hKleGL
  have hKpos : 0 < Nat.card K := Nat.card_pos
  exact hK (by omega)

/-- Clifford homogeneity and the literal seven-part of the local affine
complement force every translation-carried ambient minimal normal factor in
degree eight to have binary dimension at least three, hence order at least
eight. -/
theorem degreeEight_translationMinimal_card_le_of_clifford
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (published : PublishedPrimitiveAffineSmallCatalogueData)
    (shape : BinaryAffineExceptionalShape
      (Nat.card block.Fibre) (Nat.card block.Points))
    (hr : Nat.card block.Fibre = 8)
    (hsoluble : IsSolvable (P.complement (origin block)))
    (i₀ : block.Points)
    (N : BinaryAffineLiteralNormalAxis (preE7NonPairAction w U))
    (hretained : ¬ E block P ≤ N.1)
    (M : Subgroup (preE7NonPairAction w U ⧸ N.1))
    (hM : IsMinimalNormalSubgroup M)
    (hME : M ≤ binaryAffineTranslationImage block P N) :
    8 ≤ Nat.card M := by
  let S := initialState hTraceyPerm block
  let C := localTranslationChart block P
  letI : Finite C.V := Module.finite_of_finite (ZMod C.p)
  let N' : Subgroup S.A := N.1
  letI : N'.Normal := by
    dsimp only [N']
    exact N.2
  letI : Finite
      (ActualWreathAffineCapacity.E S (localMap block P) C).V :=
    Finite.of_injective
      (PermutationalWreathProduct.Compression.ElementarySubmodule
        (p := C.p) S.rho (localMap block P) C.equiv.symm).subtype
      (PermutationalWreathProduct.Compression.ElementarySubmodule
        (p := C.p) S.rho (localMap block P) C.equiv.symm).subtype_injective
  letI : Finite
      (ActualWreathAffineCapacity.E S
        (localMap block P) C).quotientRepresentation :=
    inferInstanceAs (Finite
      (ActualWreathAffineCapacity.E S (localMap block P) C).V)
  let normalSpace :=
    (ActualWreathAffineCapacity.originalChart S (localMap block P) C).normalSpace
      (ActualWreathAffineCapacity.pi S (localMap block P))
      (ActualWreathAffineCapacity.E S
        (localMap block P) C).quotientRepresentation N'
  letI : Finite
      (CliffordHomogeneousRestriction.sectionTopRepresentation
        S (localMap block P) C N') :=
    Finite.of_surjective normalSpace.mkQ normalSpace.mkQ_surjective
  let M' : Subgroup (S.A ⧸ N') := M
  letI : M'.Normal := by
    dsimp only [M']
    exact hM.1
  let W : Subrepresentation
      (CliffordHomogeneousRestriction.sectionTopRepresentation
        S (localMap block P) C N').ρ :=
    CliffordHomogeneousRestriction.retainedNormalConstituent
      S (localMap block P) C N' M'
  -- `Subrepresentation` is only a `SetLike`; its coercion to a type does
  -- not carry the inherited module instances.  The representation itself
  -- lives on the carrier of `toSubmodule`, so keep that literal carrier in
  -- the finite linear-group argument below.
  letI : Module (ZMod C.p) W.toSubmodule := W.toSubmodule.module
  letI : FiniteDimensional (ZMod C.p) W.toSubmodule :=
    FiniteDimensional.finiteDimensional_submodule W.toSubmodule
  letI : Finite W.toSubmodule :=
    Finite.of_injective W.toSubmodule.subtype
      W.toSubmodule.subtype_injective
  have hME' : M' ≤ CliffordHomogeneousRestriction.retainedElementaryImage
      S (localMap block P) N' := by
    simpa only [M', N', S,
      CliffordHomogeneousRestriction.retainedElementaryImage,
      CliffordHomogeneousRestriction.elementaryKernel,
      ActualWreathAffineCapacity.K, initialState] using hME
  have hMne : M' ≠ ⊥ := by
    simpa only [M'] using hM.2.1
  have hW : W ≠ ⊥ :=
    CliffordHomogeneousRestriction.retainedNormalConstituent_ne_bot
      S (localMap block P) C N' M' hME' hMne
  have hfaithful : Function.Injective
      (CliffordHomogeneousRestriction.constituentLinearKernelRepresentation
        S (localMap block P) C N' W).ρ :=
    hClifford.faithfulNonzeroConstituent
      S (localMap block P) (localMap_surjective block P) C
      (by
        rw [cliffordLocalRepresentation_rho_eq block P hTraceyPerm]
        exact binaryAffineLocalLinearRepresentation_irreducible block P)
      (by
        rw [cliffordLocalRepresentation_rho_eq block P hTraceyPerm]
        exact binaryAffineLocalLinearRepresentation_injective block P)
      (by
        intro i
        simpa only [S, CliffordHomogeneousRestriction.linearCoordinate,
          CliffordHomogeneousRestriction.linearBlockKernel, initialState,
          quotientEmbedding] using
            (binaryAffineLinearBlockKernelCoordinate_range_ne_bot
              block P published shape hsoluble i))
      N' (by
        simpa only [N', S, C,
          CliffordHomogeneousRestriction.elementaryKernel,
          ActualWreathAffineCapacity.K, initialState] using hretained)
      W hW
  have h7K : 7 ∣ Nat.card
      (CliffordHomogeneousRestriction.linearBlockKernel S (localMap block P)) := by
    simpa only [S, CliffordHomogeneousRestriction.linearBlockKernel,
      initialState, quotientEmbedding] using
        (degreeEight_seven_dvd_linearBlockKernel_card
          block P published shape hr hsoluble i₀)
  have hcardWM : Nat.card W ≤ Nat.card M := by
    simpa only [M'] using
      (CliffordHomogeneousRestriction.natCard_retainedNormalConstituent_le
        S (localMap block P) C N' M' hME')
  have hp : C.p = 2 := by
    simpa only [C, localTranslationChart] using
      (degreeEight_translationDimension block P hr).1
  let σ :=
    W.toRepresentation.comp
      (CliffordHomogeneousRestriction.linearKernelToSectionTop
        S (localMap block P) N')
  have hσ : Function.Injective σ := by
    simpa only [σ,
      CliffordHomogeneousRestriction.constituentLinearKernelRepresentation]
      using hfaithful
  have hVcard : 8 ≤ Nat.card W.toSubmodule :=
    eight_le_card_of_seven_dvd_faithful_representation hp σ hσ h7K
  exact hVcard.trans (by simpa only using hcardWM)

/-- In local degree sixteen every translation-carried ambient minimal
normal factor has binary dimension at least two.  A one-dimensional binary
constituent has trivial general linear group, whereas the literal linear
block kernel has a nonzero coordinate and acts faithfully on each nonzero
Clifford constituent. -/
theorem degreeSixteen_translationMinimal_card_le_of_clifford
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (published : PublishedPrimitiveAffineSmallCatalogueData)
    (shape : BinaryAffineExceptionalShape
      (Nat.card block.Fibre) (Nat.card block.Points))
    (hr : Nat.card block.Fibre = 16)
    (hsoluble : IsSolvable (P.complement (origin block)))
    (i₀ : block.Points)
    (N : BinaryAffineLiteralNormalAxis (preE7NonPairAction w U))
    (hretained : ¬ E block P ≤ N.1)
    (M : Subgroup (preE7NonPairAction w U ⧸ N.1))
    (hM : IsMinimalNormalSubgroup M)
    (hME : M ≤ binaryAffineTranslationImage block P N) :
    4 ≤ Nat.card M := by
  let S := initialState hTraceyPerm block
  let C := localTranslationChart block P
  letI : Finite C.V := Module.finite_of_finite (ZMod C.p)
  let N' : Subgroup S.A := N.1
  letI : N'.Normal := by
    dsimp only [N']
    exact N.2
  letI : Finite
      (ActualWreathAffineCapacity.E S (localMap block P) C).V :=
    Finite.of_injective
      (PermutationalWreathProduct.Compression.ElementarySubmodule
        (p := C.p) S.rho (localMap block P) C.equiv.symm).subtype
      (PermutationalWreathProduct.Compression.ElementarySubmodule
        (p := C.p) S.rho (localMap block P) C.equiv.symm).subtype_injective
  letI : Finite
      (ActualWreathAffineCapacity.E S
        (localMap block P) C).quotientRepresentation :=
    inferInstanceAs (Finite
      (ActualWreathAffineCapacity.E S (localMap block P) C).V)
  let normalSpace :=
    (ActualWreathAffineCapacity.originalChart S (localMap block P) C).normalSpace
      (ActualWreathAffineCapacity.pi S (localMap block P))
      (ActualWreathAffineCapacity.E S
        (localMap block P) C).quotientRepresentation N'
  letI : Finite
      (CliffordHomogeneousRestriction.sectionTopRepresentation
        S (localMap block P) C N') :=
    Finite.of_surjective normalSpace.mkQ normalSpace.mkQ_surjective
  let M' : Subgroup (S.A ⧸ N') := M
  letI : M'.Normal := by
    dsimp only [M']
    exact hM.1
  let W : Subrepresentation
      (CliffordHomogeneousRestriction.sectionTopRepresentation
        S (localMap block P) C N').ρ :=
    CliffordHomogeneousRestriction.retainedNormalConstituent
      S (localMap block P) C N' M'
  letI : Module (ZMod C.p) W.toSubmodule := W.toSubmodule.module
  letI : FiniteDimensional (ZMod C.p) W.toSubmodule :=
    FiniteDimensional.finiteDimensional_submodule W.toSubmodule
  letI : Finite W.toSubmodule :=
    Finite.of_injective W.toSubmodule.subtype
      W.toSubmodule.subtype_injective
  have hME' : M' ≤ CliffordHomogeneousRestriction.retainedElementaryImage
      S (localMap block P) N' := by
    simpa only [M', N', S,
      CliffordHomogeneousRestriction.retainedElementaryImage,
      CliffordHomogeneousRestriction.elementaryKernel,
      ActualWreathAffineCapacity.K, initialState] using hME
  have hMne : M' ≠ ⊥ := by
    simpa only [M'] using hM.2.1
  have hW : W ≠ ⊥ :=
    CliffordHomogeneousRestriction.retainedNormalConstituent_ne_bot
      S (localMap block P) C N' M' hME' hMne
  have hfaithful : Function.Injective
      (CliffordHomogeneousRestriction.constituentLinearKernelRepresentation
        S (localMap block P) C N' W).ρ :=
    hClifford.faithfulNonzeroConstituent
      S (localMap block P) (localMap_surjective block P) C
      (by
        rw [cliffordLocalRepresentation_rho_eq block P hTraceyPerm]
        exact binaryAffineLocalLinearRepresentation_irreducible block P)
      (by
        rw [cliffordLocalRepresentation_rho_eq block P hTraceyPerm]
        exact binaryAffineLocalLinearRepresentation_injective block P)
      (by
        intro i
        simpa only [S, CliffordHomogeneousRestriction.linearCoordinate,
          CliffordHomogeneousRestriction.linearBlockKernel, initialState,
          quotientEmbedding] using
            (binaryAffineLinearBlockKernelCoordinate_range_ne_bot
              block P published shape hsoluble i))
      N' (by
        simpa only [N', S, C,
          CliffordHomogeneousRestriction.elementaryKernel,
          ActualWreathAffineCapacity.K, initialState] using hretained)
      W hW
  have hcardWM : Nat.card W ≤ Nat.card M :=
    by
      simpa only [M'] using
        (CliffordHomogeneousRestriction.natCard_retainedNormalConstituent_le
          S (localMap block P) C N' M' hME')
  have hp : C.p = 2 := by
    simpa only [C, localTranslationChart] using
      (degreeSixteen_translationDimension block P hr).1
  have hKne : Nat.card
      (CliffordHomogeneousRestriction.linearBlockKernel
        S (localMap block P)) ≠ 1 := by
    intro hKcard
    have hKcard' : Nat.card (binaryAffineLinearBlockKernel block P) = 1 := by
      simpa only [S, CliffordHomogeneousRestriction.linearBlockKernel,
        initialState, quotientEmbedding] using hKcard
    letI : Subsingleton (binaryAffineLinearBlockKernel block P) :=
      (Nat.card_eq_one_iff_unique.mp hKcard').1
    have hcoordinate :=
      binaryAffineLinearBlockKernelCoordinate_range_ne_bot
        block P published shape hsoluble i₀
    apply hcoordinate
    rw [eq_bot_iff]
    rintro x ⟨k, rfl⟩
    apply Subgroup.mem_bot.mpr
    simpa only [map_one] using congrArg
      (binaryAffineLinearBlockKernelCoordinate block P i₀)
      (Subsingleton.elim k 1)
  let σ :=
    W.toRepresentation.comp
      (CliffordHomogeneousRestriction.linearKernelToSectionTop
        S (localMap block P) N')
  have hσ : Function.Injective σ := by
    simpa only [σ,
      CliffordHomogeneousRestriction.constituentLinearKernelRepresentation]
      using hfaithful
  have hVcard : 4 ≤ Nat.card W.toSubmodule :=
    four_le_card_of_nontrivial_faithful_representation hp σ hσ hKne
  exact hVcard.trans (by simpa only using hcardWM)

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
