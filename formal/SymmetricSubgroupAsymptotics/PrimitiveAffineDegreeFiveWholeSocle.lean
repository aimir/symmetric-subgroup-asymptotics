import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourFiveSocleGenerators
import SymmetricSubgroupAsymptotics.SocleGeneratorCharacterInterval
import SymmetricSubgroupAsymptotics.BlockKernelSignCoordinates
import SymmetricSubgroupAsymptotics.PermutationalWreathElementaryCompression
import SymmetricSubgroupAsymptotics.NormalGeneratorTypeSharing
import SymmetricSubgroupAsymptotics.PrimePrimarySocleTypeSharing
import SymmetricSubgroupAsymptotics.Non2PreE7DerivedTailIntervalSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineBlockCoordinateSeparation
import SymmetricSubgroupAsymptotics.PrimeRelativeHeadZeroAbsorption
import SymmetricSubgroupAsymptotics.ElementaryNormalModuleGenerators
import SymmetricSubgroupAsymptotics.MinimalNormalCompositionCharts
import SymmetricSubgroupAsymptotics.PermutationSectionNormalGenerators
import SymmetricSubgroupAsymptotics.CliffordHomogeneousRestrictionInput
import SymmetricSubgroupAsymptotics.FiniteSocleNormalGenerators
import SymmetricSubgroupAsymptotics.Non2PreE7NaturalS4Group
import SymmetricSubgroupAsymptotics.FusionCarrierAnnihilatorYonedaFixture
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.RepresentationTheory.Maschke

/-!
# The complete whole-socle bound in affine degree five

This module stays on the literal two- or three-block affine frame.  Tracey's
published induced-module theorem normally generates every translation-carried
socle factor with one element.  The remaining ambient minimal-normal factors
embed through the actual block kernel into the literal `S₂`/`S₃` top.  Their
binary and ternary primary pieces therefore each need one character slot;
type sharing pairs those slots.  No affine action is reindexed as a separate
pre-`E7` action and no project theorem is assumed.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)

/-- The actual local complement action on the literal one-dimensional
translation module, transported through the preceding range equivalence. -/
noncomputable def degreeFiveLocalLinearRepresentation
    [Nontrivial block.Fibre] :
    Rep (ZMod P.p) (LocalQuotient block P) := by
  let C := chart block P
  letI : Fact P.p.Prime := C.primeFact
  exact Rep.of ((P.complementRepresentation
    (primitive block) C (origin block)).ρ.comp
      (degreeFiveLocalComplementEquiv block P).symm.toMonoidHom)

/-- Transport does not lose faithfulness of the literal affine complement
on its translation line. -/
theorem degreeFiveLocalLinearRepresentation_injective
    [Nontrivial block.Fibre] :
    let C := chart block P
    letI : Fact P.p.Prime := C.primeFact
    Function.Injective (degreeFiveLocalLinearRepresentation block P).ρ := by
  let C := chart block P
  letI : Fact P.p.Prime := C.primeFact
  simpa only [degreeFiveLocalLinearRepresentation] using
    ((P.complementRepresentation_injective
      (primitive block) C (origin block)).comp
        (degreeFiveLocalComplementEquiv block P).symm.injective)

/-- The transported exact local affine action remains irreducible. -/
theorem degreeFiveLocalLinearRepresentation_irreducible
    [Nontrivial block.Fibre] :
    let C := chart block P
    letI : Fact P.p.Prime := C.primeFact
    Representation.IsIrreducible
      (degreeFiveLocalLinearRepresentation block P).ρ := by
  let C := chart block P
  letI : Fact P.p.Prime := C.primeFact
  letI : Representation.IsIrreducible
      (P.complementRepresentation
        (primitive block) C (origin block)).ρ :=
    P.complementRepresentation_irreducible
      (primitive block) C (origin block)
  simpa only [degreeFiveLocalLinearRepresentation] using
    (representation_irreducible_comp
      (P.complementRepresentation
        (primitive block) C (origin block)).ρ
      (degreeFiveLocalComplementEquiv block P).symm.toMonoidHom
      (degreeFiveLocalComplementEquiv block P).symm.surjective)

/-- Pointwise form of the preceding comparison on an original local
component. -/
theorem degreeFiveLocalLinearRepresentation_apply_localMap
    [Nontrivial block.Fibre]
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (d : block.Component) (v : (chart block P).V) :
    (degreeFiveLocalLinearRepresentation block P).ρ
        (localMap block P d) v =
      (localTranslationChart block P).quotientRepresentation.ρ
        (QuotientGroup.mk' (localMap block P).ker d) v := by
  let C := localTranslationChart block P
  let δ := degreeFiveLocalComplementEquiv block P
  let c : P.complement (origin block) := δ.symm (localMap block P d)
  have hcq : complementAction block P c = localMap block P d :=
    congrArg Subtype.val (δ.apply_symm_apply (localMap block P d))
  have hlocal : localMap block P c.1 = localMap block P d := by
    apply Subtype.ext
    simpa only [localMap, MonoidHom.comp_apply,
      P.complementProjection_complement] using hcq
  have hclass : QuotientGroup.mk' (localMap block P).ker c.1 =
      QuotientGroup.mk' (localMap block P).ker d := by
    apply QuotientGroup.eq_iff_div_mem.mpr
    apply MonoidHom.mem_ker.mpr
    rw [map_div, hlocal]
    simp only [div_self']
  let e : (localMap block P).ker :=
    localKernelEquiv block P (Multiplicative.ofAdd v)
  have he : C.equiv e = Multiplicative.ofAdd v := by
    change (localKernelEquiv block P).symm
      (localKernelEquiv block P (Multiplicative.ofAdd v)) = _
    exact (localKernelEquiv block P).symm_apply_apply
      (Multiplicative.ofAdd v)
  change (P.complementRepresentation
      (primitive block) (chart block P) (origin block)).ρ c v =
    C.quotientRepresentation.ρ
      (QuotientGroup.mk' (localMap block P).ker d) v
  rw [← hclass]
  symm
  apply Multiplicative.ofAdd.injective
  change Multiplicative.ofAdd
      (C.quotientRepresentation.ρ
        (QuotientGroup.mk' (localMap block P).ker c.1) v) =
    Multiplicative.ofAdd
      ((P.complementRepresentation
        (primitive block) (chart block P) (origin block)).ρ c v)
  have heAdd : (C.equiv e).toAdd = v :=
    congrArg Multiplicative.toAdd he
  conv_lhs =>
    rw [← heAdd, C.quotientRepresentation_apply]
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

private theorem degreeFive_localTranslationChart_finrank_eq_one_early
    [Nontrivial block.Fibre]
    (hr : Nat.card block.Fibre = 5) :
    Module.finrank (ZMod (localTranslationChart block P).p)
      (localTranslationChart block P).V = 1 := by
  change Module.finrank (ZMod P.p) (chart block P).V = 1
  let C₀ := P.elementaryChart block.component_preprimitive
  letI : Fact P.p.Prime := C₀.primeFact
  letI : AddCommGroup C₀.V := C₀.addCommGroup
  letI : Module (ZMod P.p) C₀.V := C₀.module
  letI : FiniteDimensional (ZMod P.p) C₀.V := C₀.finiteDimensional
  letI : Finite C₀.V := Finite.of_injective
    (fun v : C₀.V ↦ C₀.equiv.symm (Multiplicative.ofAdd v))
    C₀.equiv.symm.injective
  have hdegree₀ : Nat.card block.Fibre = P.p ^ C₀.d := by
    simpa [PrimitiveAffineProfile.ElementaryChart.d] using
      P.degree_eq_prime_pow_finrank C₀.equiv (origin block)
  have hdegree : 5 = P.p ^ C₀.d := hr.symm.trans hdegree₀
  have hd : C₀.d = 1 :=
    (prime_pow_positive_injective (d := C₀.d) (e := 1)
      P.p_prime (by norm_num : Nat.Prime 5) C₀.d_pos (by norm_num)
      (hdegree.symm.trans (by norm_num))).2
  simpa only [C₀, chart, PrimitiveAffineProfile.ElementaryChart.d] using hd

/-- On the literal affine translation line, a local-complement element
fixing one nonzero vector is the identity.  This is the precise local fact
used below to kill every coordinate of a diagonal element; no classification
of a degree-five imprimitive group enters. -/
theorem degreeFiveLocalLinear_fixed_nonzero_eq_one
    [Nontrivial block.Fibre]
    (hr : Nat.card block.Fibre = 5)
    (c : LocalQuotient block P)
    (v : (chart block P).V) (hv : v ≠ 0)
    (hfix : (degreeFiveLocalLinearRepresentation block P).ρ c v = v) :
    c = 1 := by
  let C := chart block P
  letI : Fact P.p.Prime := C.primeFact
  apply degreeFiveLocalLinearRepresentation_injective block P
  apply DFunLike.ext
  intro y
  have hdim : Module.finrank (ZMod P.p) (chart block P).V = 1 := by
    simpa only [localTranslationChart] using
      (degreeFive_localTranslationChart_finrank_eq_one_early block P hr)
  obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one hdim hv y
  let ρ := (degreeFiveLocalLinearRepresentation block P).ρ
  have hone : ρ 1 (a • v) = (a • v : (chart block P).V) := by
    simpa only [one_apply] using
      congrArg (fun f => f (a • v)) (map_one ρ)
  rw [← ha]
  change ρ c (a • v) = ρ 1 (a • v)
  have hc : ρ c (a • v) = (a • v : (chart block P).V) := by
    exact (LinearMap.map_smul (ρ c) a v).trans
      (congrArg (fun z : (chart block P).V => a • z) hfix)
  exact hc.trans hone.symm

/-- Conjugation of a literal translation coordinate by an element fixing
the displayed block is exactly the transported local affine action. -/
theorem degreeFive_coordinate_conjugation_of_top_fixed
    [Nontrivial block.Fibre]
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (g : preE7NonPairAction w U) (e : E block P)
    (i : block.Points)
    (hgi : block.topMap g • i = i) :
    (coordinate block P i (MulAut.conjNormal g e)).toAdd =
      (degreeFiveLocalLinearRepresentation block P).ρ
        (localMap block P ((ambientEmbedding block g).left i))
        (coordinate block P i e).toAdd := by
  let C := localTranslationChart block P
  let k : (localMap block P).ker :=
    PermutationalWreathProduct.Compression.kernelCoordinate
      (ambientEmbedding block) (localMap block P) i e
  have heRight : (ambientEmbedding block e.1).right = 1 :=
    ((PermutationalWreathProduct.mem_mapBase_ker_iff
      (localMap block P) (ambientEmbedding block e.1)).mp e.2).1
  have hgRight : (ambientEmbedding block g).right • i = i := by
    simpa only [ambientEmbedding, ActualBlockWreathEmbedding.embedding]
      using hgi
  have hraw :
      PermutationalWreathProduct.Compression.kernelCoordinate
          (ambientEmbedding block) (localMap block P) i
          (MulAut.conjNormal g e) =
        MulAut.conjNormal ((ambientEmbedding block g).left i) k := by
    apply Subtype.ext
    change (ambientEmbedding block (g * e.1 * g⁻¹)).left i =
      (ambientEmbedding block g).left i *
        (ambientEmbedding block e.1).left i *
          ((ambientEmbedding block g).left i)⁻¹
    rw [map_mul, map_mul, map_inv]
    exact PermutationalWreathProduct.conj_left_of_fixed
      (ambientEmbedding block g) (ambientEmbedding block e.1)
      i hgRight heRight
  have haction := C.quotientRepresentation_apply
    ((ambientEmbedding block g).left i) k
  rw [degreeFiveLocalLinearRepresentation_apply_localMap
    block P hTraceyPerm]
  change (C.equiv
      (PermutationalWreathProduct.Compression.kernelCoordinate
        (ambientEmbedding block) (localMap block P) i
        (MulAut.conjNormal g e))).toAdd = _
  rw [hraw]
  exact haction.symm

/-- The elementary chart on the global correlated translation subgroup
retains the literal coordinate function. -/
@[simp] theorem degreeFive_elementaryChart_equiv_coordinate
    [Nontrivial block.Fibre]
    (e : E block P) (i : block.Points) :
    ((elementaryChart block P).equiv e).toAdd.1 i =
      (coordinate block P i e).toAdd :=
  rfl

/-- Every nonzero invariant subspace of the actual correlated degree-five
translation module has a nonzero vector in every block coordinate.  This
uses only transitivity of the literal block top and the exact wreath
conjugation formula. -/
theorem degreeFive_nonzeroSubrepresentation_coordinate_surjective_support
    [Nontrivial block.Fibre]
    (J : Subrepresentation
      (elementaryChart block P).quotientRepresentation.ρ)
    (hJ : J ≠ ⊥) (i : block.Points) :
    ∃ e : E block P,
      ((elementaryChart block P).equiv e).toAdd ∈ J ∧
        coordinate block P i e ≠ 1 := by
  let C := elementaryChart block P
  have hJsub : J.toSubmodule ≠ ⊥ := by
    intro hbot
    apply hJ
    apply Subrepresentation.toSubmodule_injective
    exact hbot
  obtain ⟨v, hvJ, hv⟩ := J.toSubmodule.ne_bot_iff.mp hJsub
  have hsome : ∃ i₀ : block.Points, v.1 i₀ ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hv
    apply Subtype.ext
    funext i₀
    exact hall i₀
  obtain ⟨i₀, hi₀⟩ := hsome
  obtain ⟨e₀, he₀⟩ := C.equiv.surjective (Multiplicative.ofAdd v)
  letI : MulAction.IsPretransitive block.Top block.Points :=
    block.top_pretransitive
  obtain ⟨q, hq⟩ := MulAction.exists_smul_eq block.Top i₀ i
  obtain ⟨g, hg⟩ := q.2
  let e : E block P := MulAut.conjNormal g e₀
  refine ⟨e, ?_, ?_⟩
  · have hvJ' := J.apply_mem_toSubmodule
      (QuotientGroup.mk' (E block P) g) hvJ
    have he₀add : (C.equiv e₀).toAdd = v :=
      congrArg Multiplicative.toAdd he₀
    change (C.equiv (MulAut.conjNormal g e₀)).toAdd ∈ J
    rw [← C.quotientRepresentation_apply g e₀, he₀add]
    exact hvJ'
  · intro hzero
    have hraw :
        (ambientEmbedding block g).left i *
            (ambientEmbedding block e₀.1).left i₀ *
              ((ambientEmbedding block g).left i)⁻¹ = 1 := by
      have heRight : (ambientEmbedding block e₀.1).right = 1 :=
        ((PermutationalWreathProduct.mem_mapBase_ker_iff
          (localMap block P) (ambientEmbedding block e₀.1)).mp e₀.2).1
      have hformula :
          (ambientEmbedding block (g * e₀.1 * g⁻¹)).left i =
            (ambientEmbedding block g).left i *
              (ambientEmbedding block e₀.1).left i₀ *
                ((ambientEmbedding block g).left i)⁻¹ := by
        have hgRight : (ambientEmbedding block g).right • i₀ = i := by
          change block.topMap g • i₀ = i
          rw [hg]
          exact hq
        rw [← hgRight, map_mul, map_mul, map_inv]
        simp [PermutationalWreathProduct.mul_left,
          PermutationalWreathProduct.mul_right,
          PermutationalWreathProduct.inv_left, heRight, smul_smul]
      rw [← hformula]
      have hkernel :
          PermutationalWreathProduct.Compression.kernelCoordinate
              (ambientEmbedding block) (localMap block P) i e = 1 := by
        apply (localKernelEquiv block P).symm.injective
        simpa only [coordinate, MonoidHom.comp_apply, map_one] using hzero
      exact congrArg Subtype.val hkernel
    have hlocalZero : (ambientEmbedding block e₀.1).left i₀ = 1 := by
      exact (conj_eq_one_iff.mp hraw)
    have hcoordinateZero : coordinate block P i₀ e₀ = 1 := by
      apply (localKernelEquiv block P).injective
      change (localKernelEquiv block P)
          ((localKernelEquiv block P).symm
            (PermutationalWreathProduct.Compression.kernelCoordinate
              (ambientEmbedding block) (localMap block P) i₀ e₀)) =
        localKernelEquiv block P 1
      rw [(localKernelEquiv block P).apply_symm_apply, map_one]
      apply Subtype.ext
      exact hlocalZero
    apply hi₀
    have heval := congrArg
      (fun z : Multiplicative C.V ↦ z.toAdd.1 i₀) he₀
    have heval' : (0 : (chart block P).V) = v.1 i₀ := by
      simpa only [C, degreeFive_elementaryChart_equiv_coordinate,
        hcoordinateZero, map_one, toAdd_one] using heval
    exact heval'.symm

/-! ## The actual degree-five translation section

The degree-five residual needs the normal generators of the section carried
by the literal intersection with the block translations.  We first record
the exact representation statement, before converting module generators to
ambient normal generators.  This keeps the block system, the correlated
translation submodule, and every literal quotient axis visible in the type.
-/

/-- The local translation chart in affine degree five is one-dimensional
over its literal prime field. -/
theorem degreeFive_localTranslationChart_finrank_eq_one
    [Nontrivial block.Fibre]
    (hr : Nat.card block.Fibre = 5) :
    Module.finrank (ZMod (localTranslationChart block P).p)
      (localTranslationChart block P).V = 1 := by
  change Module.finrank (ZMod P.p) (chart block P).V = 1
  let C₀ := P.elementaryChart block.component_preprimitive
  letI : Fact P.p.Prime := C₀.primeFact
  letI : AddCommGroup C₀.V := C₀.addCommGroup
  letI : Module (ZMod P.p) C₀.V := C₀.module
  letI : FiniteDimensional (ZMod P.p) C₀.V := C₀.finiteDimensional
  letI : Finite C₀.V := Finite.of_injective
    (fun v : C₀.V ↦ C₀.equiv.symm (Multiplicative.ofAdd v))
    C₀.equiv.symm.injective
  have hdegree₀ : Nat.card block.Fibre = P.p ^ C₀.d := by
    simpa [PrimitiveAffineProfile.ElementaryChart.d] using
      P.degree_eq_prime_pow_finrank C₀.equiv (origin block)
  have hdegree : 5 = P.p ^ C₀.d := hr.symm.trans hdegree₀
  have hd : C₀.d = 1 :=
    (prime_pow_positive_injective (d := C₀.d) (e := 1)
      P.p_prime (by norm_num : Nat.Prime 5) C₀.d_pos (by norm_num)
      (hdegree.symm.trans (by norm_num))).2
  simpa only [C₀, chart, PrimitiveAffineProfile.ElementaryChart.d] using hd

/-- Uniform form of the preceding actual-frame calculation.  Every
invariant subspace of the correlated translation intersection is generated
by one vector at two or three blocks. -/
theorem degreeFiveTranslationAmbient_uniform_one
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    [Nontrivial block.Fibre]
    (hr : Nat.card block.Fibre = 5)
    (hs : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3)
    (i₀ : block.Points) :
    UniformSubrepresentationGeneratorBound
      (ActualWreathAffineCapacity.ambientRepresentation
        (initialState hTraceyPerm block) (localMap block P)
        (localTranslationChart block P))
      1 := by
  let S := initialState hTraceyPerm block
  let C := localTranslationChart block P
  have hindex : 2 ≤ (S.topPointStabilizer i₀).index := by
    rw [S.topPointStabilizer_index i₀]
    simpa only [Fintype.card_eq_nat_card] using block.degrees_ge_two.2
  have hlocal := hTraceyHalf C.p S.A (S.topPointStabilizer i₀) hindex
    C.V (ActualWreathAffineCapacity.localRepresentation S
      (localMap block P) C i₀)
  have hambient := hlocal.of_injective
    (ActualWreathAffineCapacity.inducedIntertwiner S
      (localMap block P) C i₀)
    (ActualWreathAffineCapacity.inducedIntertwiner_injective S
      (localMap block P) C i₀)
  have hdim : Module.finrank (ZMod C.p) C.V = 1 := by
    simpa only [C] using
      degreeFive_localTranslationChart_finrank_eq_one block P hr
  have hslots : (S.topPointStabilizer i₀).index / 2 = 1 := by
    rw [S.topPointStabilizer_index i₀, Fintype.card_eq_nat_card]
    rcases hs with hs | hs <;> rw [hs] <;> norm_num
  have htotal : Module.finrank (ZMod C.p) C.V *
      (S.topPointStabilizer i₀).index / 2 = 1 := by
    rw [hdim, one_mul, hslots]
  rw [htotal] at hambient
  simpa only [S, C] using hambient

/-- Exact cardinality of the compressed local complement. -/
theorem degreeFive_localQuotient_card_eq_complement
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre] :
    Nat.card (LocalQuotient block P) =
      Nat.card (P.complement (origin block)) := by
  exact Nat.card_congr
    (degreeFiveLocalComplementEquiv block P).symm.toEquiv

/-- The compressed local complement in affine degree five has order
dividing four. -/
theorem degreeFive_localQuotient_card_dvd_four
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (hr : Nat.card block.Fibre = 5) :
    Nat.card (LocalQuotient block P) ∣ 4 := by
  rw [degreeFive_localQuotient_card_eq_complement block P]
  exact degreeFive_complement_card_dvd_four block P hr

/-- The underlying finite set of the actual permutational wreath product is
the literal product of its base functions and its top. -/
def permutationalWreathProductEquivProd
    (D Q I : Type) [Group D] [Group Q] [MulAction Q I] :
    PermutationalWreathProduct D Q I ≃ (I → D) × Q where
  toFun x := (x.left, x.right)
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- In either residual degree-five block count, the actual quotient
`R=U/E` has order prime to five.  This is proved from its literal wreath
embedding, not from an abstract order bound for the original action. -/
theorem degreeFive_complementQuotient_coprime_five
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    (hr : Nat.card block.Fibre = 5)
    (hs : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3) :
    Nat.Coprime 5 (Nat.card
      (preE7NonPairAction w U ⧸ E block P)) := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hr]; norm_num)
  let W := PermutationalWreathProduct (LocalQuotient block P)
    block.Top block.Points
  have hRdvd : Nat.card (preE7NonPairAction w U ⧸ E block P) ∣
      Nat.card W :=
    Subgroup.card_dvd_of_injective (quotientEmbedding block P)
      (quotientEmbedding_injective block P)
  have hlocal : Nat.card (LocalQuotient block P) ∣ 4 :=
    degreeFive_localQuotient_card_dvd_four block P hr
  have htop : Nat.card block.Top ∣ (Nat.card block.Points).factorial := by
    have h := Subgroup.card_dvd_of_injective block.Top.subtype
      (show Function.Injective block.Top.subtype from Subtype.val_injective)
    simpa only [Nat.card_eq_fintype_card, Fintype.card_perm] using h
  have hWcard : Nat.card W =
      Nat.card (LocalQuotient block P) ^ Nat.card block.Points *
        Nat.card block.Top := by
    rw [Nat.card_congr
      (permutationalWreathProductEquivProd
        (LocalQuotient block P) block.Top block.Points), Nat.card_prod,
      Nat.card_fun]
  have hWdvd : Nat.card W ∣
      4 ^ Nat.card block.Points * (Nat.card block.Points).factorial := by
    rw [hWcard]
    obtain ⟨k, hk⟩ := hlocal
    exact Nat.mul_dvd_mul
      ⟨k ^ Nat.card block.Points, by rw [hk, mul_pow]⟩ htop
  apply Nat.prime_five.coprime_iff_not_dvd.mpr
  intro hfive
  have : 5 ∣ 4 ^ Nat.card block.Points *
      (Nat.card block.Points).factorial :=
    hfive.trans (hRdvd.trans hWdvd)
  rcases hs with hs | hs <;> rw [hs] at this <;> norm_num at this

/-- In the two residual block counts the actual translation intersection
is nontrivial.  Transitivity supplies a factor five in the original group,
whereas the literal complement quotient just proved has five-prime order. -/
theorem degreeFive_translationIntersection_ne_bot
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    (hr : Nat.card block.Fibre = 5)
    (hs : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3) :
    E block P ≠ ⊥ := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hr]; norm_num)
  intro hE
  have hw : w = 5 * Nat.card block.Points := by
    simpa only [hr] using width_eq block
  have hwdiv : w ∣ Nat.card (preE7NonPairAction w U) := by
    simpa only [Nat.card_fin] using
      (transitive_natCard_dvd_group_natCard
        (B := preE7NonPairAction w U) (X := Fin w) basePoint)
  have hfiveU : 5 ∣ Nat.card (preE7NonPairAction w U) := by
    have h5w : 5 ∣ w := by
      refine ⟨Nat.card block.Points, ?_⟩
      exact hw
    exact h5w.trans hwdiv
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (E block P)
  have hEcard : Nat.card (E block P) = 1 := by
    rw [hE, Subgroup.card_bot]
  have hcardEq : Nat.card (preE7NonPairAction w U ⧸ E block P) =
      Nat.card (preE7NonPairAction w U) := by
    rw [hEcard, mul_one] at hmul
    exact hmul.symm
  have hfiveR : 5 ∣
      Nat.card (preE7NonPairAction w U ⧸ E block P) := by
    rw [hcardEq]
    exact hfiveU
  exact (Nat.prime_five.coprime_iff_not_dvd.mp
    (degreeFive_complementQuotient_coprime_five block P hr hs)) hfiveR

/-- The literal global translation intersection is a five-group. -/
theorem degreeFive_translationIntersection_isPGroup
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    (hr : Nat.card block.Fibre = 5) :
    IsPGroup 5 (E block P) := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hr]; norm_num)
  let C := elementaryChart block P
  letI : Fact C.p.Prime := C.primeFact
  letI : Finite C.V := Module.finite_of_finite (ZMod C.p)
  have hcard : Nat.card (E block P) = C.p ^
      Module.finrank (ZMod C.p) C.V := by
    calc
      Nat.card (E block P) = Nat.card (Multiplicative C.V) :=
        Nat.card_congr C.equiv.toEquiv
      _ = Nat.card C.V := rfl
      _ = C.p ^ Module.finrank (ZMod C.p) C.V := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod C.p), Nat.card_zmod]
  have hp : C.p = 5 := by
    change P.p = 5
    exact degreeFive_profilePrime_eq_five block P hr
  apply IsPGroup.of_card
  simpa only [hp] using hcard

/-- One literal normal axis for the degree-five retained interval. -/
abbrev DegreeFiveLiteralNormalAxis :=
  {N : Subgroup (preE7NonPairAction w U) // N.Normal}

/-- The actual translation section retained in the quotient `U/N`. -/
abbrev degreeFiveTranslationImage
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U)) :
    Subgroup (preE7NonPairAction w U ⧸ N.1) :=
  (E block P).map (QuotientGroup.mk' N.1)

instance degreeFiveTranslationImage_normal
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U)) :
    (degreeFiveTranslationImage block P N).Normal := by
  dsimp only [degreeFiveTranslationImage]
  infer_instance

/-- Pull a translation-carried normal subgroup of a retained quotient back
to the exact correlated translation module in the original action. -/
abbrev degreeFiveTranslationPreimage
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U))
    (H : Subgroup (preE7NonPairAction w U ⧸ N.1)) :
    Subgroup (preE7NonPairAction w U) :=
  H.comap (QuotientGroup.mk' N.1) ⊓ E block P

instance degreeFiveTranslationPreimage_normal
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U))
    (H : Subgroup (preE7NonPairAction w U ⧸ N.1)) [H.Normal] :
    (degreeFiveTranslationPreimage block P N H).Normal := by
  dsimp only [degreeFiveTranslationPreimage]
  infer_instance

theorem degreeFiveTranslationPreimage_le_translation
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U))
    (H : Subgroup (preE7NonPairAction w U ⧸ N.1)) :
    degreeFiveTranslationPreimage block P N H ≤ E block P :=
  inf_le_right

/-- A translation-carried subgroup is exactly the image of its literal
pullback inside `E`. -/
theorem degreeFiveTranslationPreimage_map_eq
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U))
    (H : Subgroup (preE7NonPairAction w U ⧸ N.1))
    (hH : H ≤ degreeFiveTranslationImage block P N) :
    (degreeFiveTranslationPreimage block P N H).map
        (QuotientGroup.mk' N.1) = H := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact hx.1
  · intro y hy
    obtain ⟨e, heE, he⟩ := hH hy
    refine ⟨e, ⟨?_, heE⟩, he⟩
    change QuotientGroup.mk' N.1 e ∈ H
    simpa only [he] using hy

/-- Every normal subgroup carried by the retained translation section is
normally generated by one element.  The proof stays on the literal block
system: pull the subgroup back to the correlated translation module, apply
Tracey's one-vector theorem to the corresponding normal subrepresentation,
and map the resulting normal generator to the retained quotient. -/
theorem degreeFiveTranslationCarried_normalGen_le_one
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (hr : Nat.card block.Fibre = 5)
    (hs : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3)
    (i₀ : block.Points)
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U))
    (H : Subgroup (preE7NonPairAction w U ⧸ N.1)) [H.Normal]
    (hH : H ≤ degreeFiveTranslationImage block P N) :
    MarkedC4.normalGen H ≤ 1 := by
  let L := degreeFiveTranslationPreimage block P N H
  have hLgen : MarkedC4.normalGen L ≤ 1 := by
    apply normalGen_le_of_elementaryNormalSubrepresentation_comp_generated
      (E block P) (elementaryChart block P) L
      (degreeFiveTranslationPreimage_le_translation block P N H)
    have huniform := degreeFiveTranslationAmbient_uniform_one
      block P hTraceyHalf hTraceyPerm hr hs i₀
    let M₀ := (elementaryChart block P).originalKernelChart
      |>.normalSubrepresentation (QuotientGroup.mk' (E block P))
        (QuotientGroup.mk'_surjective (E block P))
        (elementaryChart block P).quotientRepresentation L
    let M := ActualWreathAffineCapacity.subrepresentationComp
      (QuotientGroup.mk' (E block P))
      (elementaryChart block P).quotientRepresentation.ρ M₀
    have hM := huniform M
    simpa only [ActualWreathAffineCapacity.ambientRepresentation,
      initialState, localTranslationChart, elementaryChart,
      ActualWreathAffineCapacity.E,
      PermutationalWreathProduct.Compression.kernelElementaryChart,
      M, M₀] using hM
  rw [← degreeFiveTranslationPreimage_map_eq block P N H hH]
  exact (MarkedC4.normalGen_map_le (QuotientGroup.mk' N.1)
    (QuotientGroup.mk'_surjective N.1) L).trans hLgen

/-- The actual correlated translation intersection has exponent five. -/
theorem degreeFive_translation_pow_five
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (hr : Nat.card block.Fibre = 5) (x : E block P) : x ^ 5 = 1 := by
  apply (translationMulEquiv block P).injective
  apply Multiplicative.toAdd.injective
  simp only [map_pow, map_one, toAdd_pow, toAdd_one]
  change 5 • ((translationMulEquiv block P x).toAdd) = 0
  rw [← degreeFive_profilePrime_eq_five block P hr]
  exact ZModModule.char_nsmul_eq_zero P.p _

/-- The literal correlated translation intersection is abelian because its
actual coordinate chart is an additive vector space. -/
theorem degreeFive_translation_commute
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (x y : E block P) : Commute x y := by
  rw [Commute]
  apply (translationMulEquiv block P).injective
  simp only [map_mul]
  exact mul_comm (translationMulEquiv block P x)
    (translationMulEquiv block P y)

/-- Every retained degree-five translation section still has exponent
five. -/
theorem degreeFiveTranslationImage_pow_five
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (hr : Nat.card block.Fibre = 5)
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U))
    (x : degreeFiveTranslationImage block P N) : x ^ 5 = 1 := by
  let q := QuotientGroup.mk' N.1
  let f : E block P →* degreeFiveTranslationImage block P N :=
    q.subgroupMap (E block P)
  obtain ⟨x₀, rfl⟩ := MonoidHom.subgroupMap_surjective q (E block P) x
  rw [← map_pow, degreeFive_translation_pow_five block P hr, map_one]

/-- Every retained image of the correlated translation intersection remains
abelian. -/
theorem degreeFiveTranslationImage_commute
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U))
    (x y : degreeFiveTranslationImage block P N) : Commute x y := by
  let q := QuotientGroup.mk' N.1
  let f : E block P →* degreeFiveTranslationImage block P N :=
    q.subgroupMap (E block P)
  obtain ⟨x₀, rfl⟩ := MonoidHom.subgroupMap_surjective q (E block P) x
  obtain ⟨y₀, rfl⟩ := MonoidHom.subgroupMap_surjective q (E block P) y
  exact (degreeFive_translation_commute block P x₀ y₀).map f

/-- A retained axis has a nonzero translation section exactly when it does
not kill the literal intersection `E`. -/
theorem degreeFiveTranslationImage_ne_bot
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U))
    (hretained : ¬ E block P ≤ N.1) :
    degreeFiveTranslationImage block P N ≠ ⊥ := by
  intro hbot
  apply hretained
  have hle : E block P ≤ (QuotientGroup.mk' N.1).ker :=
    (Subgroup.map_eq_bot_iff
      (H := E block P) (f := QuotientGroup.mk' N.1)).mp hbot
  simpa only [QuotientGroup.ker_mk'] using hle

/-- Passing to a retained quotient cannot enlarge the correlated
translation section. -/
theorem degreeFiveTranslationImage_card_le
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (hr : Nat.card block.Fibre = 5)
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U)) :
    Nat.card (degreeFiveTranslationImage block P N) ≤
      5 ^ Nat.card block.Points := by
  let C := chart block P
  letI : Fact P.p.Prime := C.primeFact
  letI : Finite C.V := Module.finite_of_finite (ZMod P.p)
  have hV : Nat.card (chart block P).V = 5 := by
    calc
      Nat.card (chart block P).V =
          Nat.card (Multiplicative (chart block P).V) := rfl
      _ = Nat.card P.V :=
        Nat.card_congr (chart block P).equiv.symm.toEquiv
      _ = Nat.card block.Fibre := P.card_eq (origin block)
      _ = 5 := hr
  calc
    Nat.card (degreeFiveTranslationImage block P N) ≤ Nat.card (E block P) :=
      Nat.card_le_card_of_surjective
        ((QuotientGroup.mk' N.1).subgroupMap (E block P))
        (MonoidHom.subgroupMap_surjective _ _)
    _ ≤ Nat.card (Multiplicative
        (block.Points → (chart block P).V)) :=
      Nat.card_le_card_of_injective (coordinates block P)
        (coordinates_injective block P)
    _ = Nat.card (block.Points → (chart block P).V) := rfl
    _ = Nat.card (chart block P).V ^ Nat.card block.Points := by
      rw [Nat.card_fun]
    _ = 5 ^ Nat.card block.Points := by rw [hV]

/-- The retained translation image remains a five-group. -/
theorem degreeFiveTranslationImage_isPGroup
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    (hr : Nat.card block.Fibre = 5)
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U)) :
    IsPGroup 5 (degreeFiveTranslationImage block P N) := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hr]; norm_num)
  exact (degreeFive_translationIntersection_isPGroup block P hr).map
    (QuotientGroup.mk' N.1)

/-- The quotient of a retained axis by its translation image is a literal
quotient of `U/E`.  This map is the exact third-isomorphism arrow needed to
transfer the prime-to-five order statement; no abstract quotient model is
chosen. -/
def degreeFiveTranslationResidualMap
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U)) :
    (preE7NonPairAction w U ⧸ E block P) →*
      ((preE7NonPairAction w U ⧸ N.1) ⧸
        degreeFiveTranslationImage block P N) :=
  QuotientGroup.lift (E block P)
    ((QuotientGroup.mk' (degreeFiveTranslationImage block P N)).comp
      (QuotientGroup.mk' N.1)) (by
        intro e he
        apply (QuotientGroup.eq_one_iff _).mpr
        exact ⟨e, he, rfl⟩)

/-- The exact residual map is onto. -/
theorem degreeFiveTranslationResidualMap_surjective
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U)) :
    Function.Surjective (degreeFiveTranslationResidualMap block P N) := by
  intro z
  obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective
    (degreeFiveTranslationImage block P N) z
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N.1 q
  exact ⟨QuotientGroup.mk' (E block P) g, rfl⟩

/-- Every retained quotient above the translation image has order prime to
five, because it is an actual quotient of the already-constructed monomial
complement `U/E`. -/
theorem degreeFiveTranslationResidual_coprime_five
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    (hr : Nat.card block.Fibre = 5)
    (hs : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3)
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U)) :
    Nat.Coprime 5 (Nat.card
      ((preE7NonPairAction w U ⧸ N.1) ⧸
        degreeFiveTranslationImage block P N)) := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hr]; norm_num)
  have hdiv : Nat.card
      ((preE7NonPairAction w U ⧸ N.1) ⧸
        degreeFiveTranslationImage block P N) ∣
      Nat.card (preE7NonPairAction w U ⧸ E block P) :=
    Subgroup.card_dvd_of_surjective
      (degreeFiveTranslationResidualMap block P N)
      (degreeFiveTranslationResidualMap_surjective block P N)
  exact Nat.Coprime.of_dvd_right hdiv
    (degreeFive_complementQuotient_coprime_five block P hr hs)

/-- On ambient minimal normal factors of a retained quotient, being a
five-group is equivalent to being physically carried by the translation
image.  This identifies the literal frame split with the generic
prime-primary type split. -/
theorem degreeFive_minimalNormal_isPGroup_five_iff_le_translationImage
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    (hr : Nat.card block.Fibre = 5)
    (hs : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3)
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U))
    (M : Subgroup (preE7NonPairAction w U ⧸ N.1))
    (_hM : IsMinimalNormalSubgroup M) :
    IsPGroup 5 M ↔ M ≤ degreeFiveTranslationImage block P N := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let q := QuotientGroup.mk' (degreeFiveTranslationImage block P N)
  constructor
  · intro hMp
    have himage : IsPGroup 5 (M.map q) := hMp.map q
    obtain ⟨d, hd⟩ := himage.exists_card_eq
    have himageDvd : Nat.card (M.map q) ∣
        Nat.card ((preE7NonPairAction w U ⧸ N.1) ⧸
          degreeFiveTranslationImage block P N) :=
      Subgroup.card_dvd_of_injective (M.map q).subtype
        (show Function.Injective (M.map q).subtype from Subtype.val_injective)
    have hcopPow : Nat.Coprime (5 ^ d)
        (Nat.card ((preE7NonPairAction w U ⧸ N.1) ⧸
          degreeFiveTranslationImage block P N)) :=
      (degreeFiveTranslationResidual_coprime_five block P hr hs N).pow_left d
    have hcardOne : Nat.card (M.map q) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcopPow (hd ▸ dvd_rfl) himageDvd
    have hmapBot : M.map q = ⊥ := by
      rw [← Subgroup.card_eq_one]
      exact hcardOne
    have hker : M ≤ q.ker :=
      (Subgroup.map_eq_bot_iff (H := M) (f := q)).mp hmapBot
    simpa only [q, QuotientGroup.ker_mk'] using hker
  · intro hMV
    exact (degreeFiveTranslationImage_isPGroup block P hr N).to_le hMV

/-- The ambient-minimal translation factors on one retained degree-five
axis. -/
abbrev degreeFiveTranslationSoclePart
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U)) :
    Subgroup (preE7NonPairAction w U ⧸ N.1) :=
  finiteGroupSoclePart (preE7NonPairAction w U ⧸ N.1)
    (degreeFiveTranslationImage block P N)

/-- The complementary prime-to-five ambient socle types. -/
abbrev degreeFiveOuterSoclePart
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U)) :
    Subgroup (preE7NonPairAction w U ⧸ N.1) :=
  minimalNormalSoclePart (preE7NonPairAction w U ⧸ N.1)
    (fun M ↦ ¬ IsPGroup 5 M)

/-- A non-five-primary ambient minimal factor is disjoint from the literal
translation image.  This is an internal minimal-normal argument; it does
not use a complement chosen by Schur--Zassenhaus. -/
theorem degreeFiveOuterMinimal_inf_translationImage
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    (hr : Nat.card block.Fibre = 5)
    (hs : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3)
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U))
    (M : Subgroup (preE7NonPairAction w U ⧸ N.1))
    (hM : IsMinimalNormalSubgroup M)
    (houter : ¬ IsPGroup 5 M) :
    M ⊓ degreeFiveTranslationImage block P N = ⊥ := by
  letI : M.Normal := hM.1
  have hnot : ¬ M ≤ degreeFiveTranslationImage block P N := by
    intro hle
    exact houter ((degreeFive_minimalNormal_isPGroup_five_iff_le_translationImage
      block P hr hs N M hM).2 hle)
  by_contra hne
  have hEq : M ⊓ degreeFiveTranslationImage block P N = M :=
    hM.2.2 (M ⊓ degreeFiveTranslationImage block P N)
      (inferInstance : (M ⊓ degreeFiveTranslationImage block P N).Normal)
      hne inf_le_left
  exact hnot (by rw [← hEq]; exact inf_le_right)

/-- Every outer ambient minimal factor centralizes the retained translation
section.  Both subgroups are normal, so their commutator lies in their
just-proved trivial intersection. -/
theorem degreeFiveOuterMinimal_le_translationCentralizer
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    (hr : Nat.card block.Fibre = 5)
    (hs : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3)
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U))
    (M : Subgroup (preE7NonPairAction w U ⧸ N.1))
    (hM : IsMinimalNormalSubgroup M)
    (houter : ¬ IsPGroup 5 M) :
    M ≤ Subgroup.centralizer
      (degreeFiveTranslationImage block P N :
        Set (preE7NonPairAction w U ⧸ N.1)) := by
  letI : M.Normal := hM.1
  apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
  apply le_bot_iff.mp
  have hle : ⁅M, degreeFiveTranslationImage block P N⁆ ≤
      M ⊓ degreeFiveTranslationImage block P N :=
    le_inf (Subgroup.commutator_le_left _ _)
      (Subgroup.commutator_le_right _ _)
  rw [degreeFiveOuterMinimal_inf_translationImage
    block P hr hs N M hM houter] at hle
  exact hle

/-- The complete outer socle sum centralizes the literal translation
section.  This packages the preceding minimal-factor statement at exactly
the subgroup consumed by the retained-top argument. -/
theorem degreeFiveOuterSoclePart_le_translationCentralizer
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    (hr : Nat.card block.Fibre = 5)
    (hs : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3)
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U)) :
    degreeFiveOuterSoclePart N ≤ Subgroup.centralizer
      (degreeFiveTranslationImage block P N :
        Set (preE7NonPairAction w U ⧸ N.1)) := by
  apply minimalNormalSoclePart_le_of
  intro M hM houter
  exact degreeFiveOuterMinimal_le_translationCentralizer
    block P hr hs N M hM houter

/-- Subgroups of coprime prime-power order intersect trivially.  The proof
is elementwise, so it does not require either subgroup to be normal. -/
theorem isPGroup_inf_eq_bot_of_coprime
    {G : Type} [Group G]
    (p q : ℕ) (hpq : Nat.Coprime p q)
    (H K : Subgroup G) (hH : IsPGroup p H) (hK : IsPGroup q K) :
    H ⊓ K = ⊥ := by
  apply le_antisymm
  · intro x hx
    let xH : H := ⟨x, hx.1⟩
    let xK : K := ⟨x, hx.2⟩
    obtain ⟨a, ha⟩ := hH xH
    obtain ⟨b, hb⟩ := hK xK
    have hpa : x ^ (p ^ a) = 1 := congrArg Subtype.val ha
    have hqb : x ^ (q ^ b) = 1 := congrArg Subtype.val hb
    have horder : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes
      ((hpq.pow_left a).pow_right b)
      (orderOf_dvd_of_pow_eq_one hpa)
      (orderOf_dvd_of_pow_eq_one hqb)
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp horder)
  · exact bot_le

/-- The prime-`p` part inside the outer degree-five socle. -/
abbrev degreeFiveOuterPrimeSoclePart
    (p : ℕ)
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U)) :
    Subgroup (preE7NonPairAction w U ⧸ N.1) :=
  minimalNormalSoclePart (preE7NonPairAction w U ⧸ N.1)
    (fun M ↦ ¬ IsPGroup 5 M ∧ IsPGroup p M)

theorem degreeFiveOuterPrimeSoclePart_isPGroup
    (p : ℕ) [Fact p.Prime]
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U)) :
    IsPGroup p (degreeFiveOuterPrimeSoclePart p N) :=
  primePrimarySoclePart_isPGroup_of_predicate p
    (preE7NonPairAction w U ⧸ N.1) (fun M ↦ ¬ IsPGroup 5 M)

theorem degreeFiveOuterPrimeSoclePart_le_outer
    (p : ℕ)
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U)) :
    degreeFiveOuterPrimeSoclePart p N ≤ degreeFiveOuterSoclePart N := by
  apply minimalNormalSoclePart_le_of
  intro M hM h
  exact minimalNormal_le_minimalNormalSoclePart
    (fun K ↦ ¬ IsPGroup 5 K) M hM h.1

/-- A non-five prime part is disjoint from the retained translation image.
This is the clean prime-primary replacement for a global order count on the
whole outer socle. -/
theorem degreeFiveOuterPrimeSoclePart_inf_translationImage
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    (hr : Nat.card block.Fibre = 5)
    (p : ℕ) [Fact p.Prime]
    (hp5 : Nat.Coprime p 5)
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U)) :
    degreeFiveOuterPrimeSoclePart p N ⊓
      degreeFiveTranslationImage block P N = ⊥ :=
  isPGroup_inf_eq_bot_of_coprime p 5 hp5 _ _
    (degreeFiveOuterPrimeSoclePart_isPGroup p N)
    (degreeFiveTranslationImage_isPGroup block P hr N)

/-- The frame-defined translation part is exactly the generic five-primary
socle part. -/
theorem degreeFiveTranslationSoclePart_eq_primePrimary
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    (hr : Nat.card block.Fibre = 5)
    (hs : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3)
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U)) :
    degreeFiveTranslationSoclePart block P N =
      minimalNormalSoclePart (preE7NonPairAction w U ⧸ N.1)
        (fun M ↦ IsPGroup 5 M) := by
  unfold degreeFiveTranslationSoclePart finiteGroupSoclePart
  apply minimalNormalSoclePart_congr
  intro M hM
  exact (degreeFive_minimalNormal_isPGroup_five_iff_le_translationImage
    block P hr hs N M hM).symm

/-- Tracey's literal induced-module estimate supplies the translation half
of the degree-five socle decomposition with no finite catalogue input. -/
theorem degreeFiveTranslationSoclePart_normalGen_le_one
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (hr : Nat.card block.Fibre = 5)
    (hs : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3)
    (i₀ : block.Points)
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U)) :
    MarkedC4.normalGen
      (degreeFiveTranslationSoclePart block P N) ≤ 1 :=
  degreeFiveTranslationCarried_normalGen_le_one
    hTraceyHalf hTraceyPerm block P hr hs i₀ N
    (degreeFiveTranslationSoclePart block P N)
    (finiteGroupSoclePart_le _ _)

/-- Five-primary and outer types share their normal-generator positions.
Thus the final degree-five structural theorem has two independent local
obligations, both with bound one. -/
theorem degreeFive_socle_normalGen_le_one_of_parts
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    (hr : Nat.card block.Fibre = 5)
    (hs : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3)
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U))
    (htranslation : MarkedC4.normalGen
      (degreeFiveTranslationSoclePart block P N) ≤ 1)
    (houter : MarkedC4.normalGen
      (degreeFiveOuterSoclePart N) ≤ 1) :
    MarkedC4.normalGen
      (finiteGroupSocle (preE7NonPairAction w U ⧸ N.1)) ≤ 1 := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hsplit := normalGen_finiteGroupSocle_le_max_primePrimaryParts 5
    (preE7NonPairAction w U ⧸ N.1)
  rw [← degreeFiveTranslationSoclePart_eq_primePrimary
      block P hr hs N] at hsplit
  exact hsplit.trans (max_le htranslation houter)

/-- Padded tuple form consumed by the complete-character interval. -/
noncomputable def degreeFive_socleNormalGeneratorBound_of_parts
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    (hr : Nat.card block.Fibre = 5)
    (hs : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3)
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U))
    (htranslation : MarkedC4.normalGen
      (degreeFiveTranslationSoclePart block P N) ≤ 1)
    (houter : MarkedC4.normalGen
      (degreeFiveOuterSoclePart N) ≤ 1) :
    SocleNormalGeneratorBound (preE7NonPairAction w U ⧸ N.1) 1 :=
  (socleNormalGeneratorBound_iff_normalGen_le
    (preE7NonPairAction w U ⧸ N.1) 1).2
      (degreeFive_socle_normalGen_le_one_of_parts
        block P hr hs N htranslation houter)

/-- A degree-five translation-carried normal section with zero complete
relative head is exactly absorbed by ambient commutators. -/
theorem degreeFive_translationSection_commutator_full_of_relativeHead_zero
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (hr : Nat.card block.Fibre = 5)
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U))
    (M : Subgroup (preE7NonPairAction w U ⧸ N.1)) [M.Normal]
    (hM : M ≤ degreeFiveTranslationImage block P N)
    (hzero : Module.finrank (ZMod 5)
      (primeRelativeCharacters 5 M) = 0) :
    ⁅M, (⊤ : Subgroup (preE7NonPairAction w U ⧸ N.1))⁆ = M := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  apply mixedCommutator_eq_of_exponent_prime_relativeHead_zero 5 M
  · intro m
    let x : degreeFiveTranslationImage block P N := ⟨m.1, hM m.2⟩
    apply Subtype.ext
    change (m.1 : preE7NonPairAction w U ⧸ N.1) ^ 5 = 1
    exact congrArg Subtype.val
      (degreeFiveTranslationImage_pow_five block P hr N x)
  · exact hzero

/-- The actual translation intersection is contained in the literal block
kernel.  This is extracted directly from the compressed wreath equation,
so it applies to correlated translation submodules. -/
theorem degreeFive_translationIntersection_le_topMap_ker
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre] :
    E block P ≤ block.topMap.ker := by
  intro e he
  apply MonoidHom.mem_ker.mpr
  have hcompressed :
      PermutationalWreathProduct.mapBase (localMap block P)
          (ambientEmbedding block e) = 1 :=
    MonoidHom.mem_ker.mp he
  have hright := congrArg PermutationalWreathProduct.right hcompressed
  simpa only [PermutationalWreathProduct.mapBase_right,
    PermutationalWreathProduct.one_right] using congrArg Subtype.val hright

/-- The literal base translation coordinate separates the degree-five
translation intersection after all ambient conjugates are retained.  Both
the kernel refinement to original block evaluation and the global
separation are consequences of the actual wreath chart; no label is left
as construction data. -/
theorem degreeFive_translationCoordinate_conjugates_separate
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (e : E block P)
    (he : ∀ a : preE7NonPairAction w U,
      coordinate block P block.base (MulAut.conjNormal a e) = 1) : e = 1 :=
  translationCoordinate_conjugates_separate block P e he

/-- Schur--Zassenhaus splits the actual translation intersection in each
residual degree-five frame.  The complement is a literal subgroup of the
original action; no splitting of its projection to the block top is
asserted. -/
theorem degreeFive_translationComplement_exists
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    (hr : Nat.card block.Fibre = 5)
    (hs : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3) :
    ∃ H : Subgroup (preE7NonPairAction w U),
      Subgroup.IsComplement' (E block P) H := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hr]; norm_num)
  have hE := degreeFive_translationIntersection_isPGroup block P hr
  obtain ⟨d, hd⟩ := hE.exists_card_eq
  have hindex : (E block P).index =
      Nat.card (preE7NonPairAction w U ⧸ E block P) :=
    (E block P).index_eq_card
  apply Subgroup.exists_right_complement'_of_coprime
  rw [hd, hindex]
  exact Nat.Coprime.pow_left d
    (degreeFive_complementQuotient_coprime_five block P hr hs)

/-! ## The actual degree-five monomial quotient -/

/-- Projection of the literal quotient `R=U/E` to the actual block top. -/
def degreeFiveQuotientTopMap
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre] :
    (preE7NonPairAction w U ⧸ E block P) →* block.Top :=
  PermutationalWreathProduct.rightHom.comp (quotientEmbedding block P)

/-- The actual diagonal block kernel in the degree-five quotient. -/
abbrev degreeFiveQuotientBlockKernel
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre] :
    Subgroup (preE7NonPairAction w U ⧸ E block P) :=
  (degreeFiveQuotientTopMap block P).ker

/-- Literal preimage in the original action of the diagonal block kernel
after translations have been removed.  It contains `E`, and quotienting by
it gives the actual block top. -/
abbrev degreeFiveBlockKernelPreimage
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre] :
    Subgroup (preE7NonPairAction w U) :=
  (degreeFiveQuotientBlockKernel block P).comap
    (QuotientGroup.mk' (E block P))

instance degreeFiveBlockKernelPreimage_normal
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre] :
    (degreeFiveBlockKernelPreimage block P).Normal := by
  dsimp only [degreeFiveBlockKernelPreimage,
    degreeFiveQuotientBlockKernel]
  infer_instance

theorem degreeFive_translation_le_blockKernelPreimage
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre] :
    E block P ≤ degreeFiveBlockKernelPreimage block P := by
  intro e he
  change QuotientGroup.mk' (E block P) e ∈
    degreeFiveQuotientBlockKernel block P
  change degreeFiveQuotientTopMap block P
    (QuotientGroup.mk' (E block P) e) = 1
  have heq : QuotientGroup.mk' (E block P) e = 1 :=
    (QuotientGroup.eq_one_iff e).mpr he
  rw [heq, map_one]

/-- Image in `Q=U/N` of the actual block kernel. -/
abbrev degreeFiveRetainedBlockKernel
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U)) :
    Subgroup (preE7NonPairAction w U ⧸ N.1) :=
  (degreeFiveBlockKernelPreimage block P).map
    (QuotientGroup.mk' N.1)

instance degreeFiveRetainedBlockKernel_normal
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U)) :
    (degreeFiveRetainedBlockKernel block P N).Normal :=
  Subgroup.Normal.map inferInstance (QuotientGroup.mk' N.1)
    (QuotientGroup.mk'_surjective N.1)

/-- The retained translation image lies in the retained block kernel. -/
theorem degreeFiveTranslationImage_le_retainedBlockKernel
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U)) :
    degreeFiveTranslationImage block P N ≤
      degreeFiveRetainedBlockKernel block P N :=
  Subgroup.map_mono (degreeFive_translation_le_blockKernelPreimage block P)

/-- Exact faithful-section statement for the degree-five residual.  It is
the literal quotient form of the manuscript identity `K ∩ D = 1`: inside
the retained block kernel, the centralizer of the nonzero translation
section consists precisely of that section. -/
def DegreeFiveFaithfulTranslationSection
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U)) : Prop :=
  Subgroup.centralizer
      (degreeFiveTranslationImage block P N :
        Set (preE7NonPairAction w U ⧸ N.1)) ⊓
      degreeFiveRetainedBlockKernel block P N =
    degreeFiveTranslationImage block P N

/-- Membership in the invariant intersection recorded by the original
elementary chart is literal membership in `N ∩ E`. -/
theorem degreeFive_elementaryChart_mem_normalSubrepresentation_iff
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U))
    (e : E block P) :
    let C := elementaryChart block P
    let A := C.quotientRepresentation
    (C.equiv e).toAdd ∈
        C.originalKernelChart.normalSubrepresentation
          (QuotientGroup.mk' (E block P))
          (QuotientGroup.mk'_surjective (E block P)) A N.1 ↔
      (e.1 : preE7NonPairAction w U) ∈ N.1 := by
  let C := elementaryChart block P
  let A := C.quotientRepresentation
  let q : preE7NonPairAction w U →*
      preE7NonPairAction w U ⧸ E block P :=
    QuotientGroup.mk' (E block P)
  let k : q.ker := C.quotientKernelEquiv (C.equiv e)
  have hkernel :
      (C.originalKernelChart.kernelCoordinates q A).ker ≤
        N.1.subgroupOf q.ker := by
    intro x hx
    have hx1 : x = 1 := by
      apply C.originalKernelChart.equiv.symm.injective
      exact (MonoidHom.mem_ker.mp hx).trans
        (map_one C.originalKernelChart.equiv.symm).symm
    subst x
    exact Subgroup.one_mem _
  have hkcoord :
      (C.originalKernelChart.kernelCoordinates q A k).toAdd =
        (C.equiv e).toAdd := by
    dsimp only [k, q, OriginalKernelModuleChart.kernelCoordinates,
      ElementaryMinimalNormalChart.originalKernelChart]
    change (C.equiv (C.equiv.symm (C.equiv e))).toAdd = _
    rw [C.equiv.apply_symm_apply]
  change (C.equiv e).toAdd ∈
      C.originalKernelChart.normalSubrepresentation q
        (QuotientGroup.mk'_surjective (E block P)) A N.1 ↔
    (e.1 : preE7NonPairAction w U) ∈ N.1
  rw [← hkcoord]
  change (C.originalKernelChart.kernelCoordinates q A k).toAdd ∈
      sectionSubgroupImage
        (C.originalKernelChart.kernelCoordinates q A)
        (N.1.subgroupOf q.ker) ↔ _
  rw [sectionSubgroupImage_mem_iff
    (C.originalKernelChart.kernelCoordinates q A)
    (N.1.subgroupOf q.ker) hkernel k]
  change (k.1 : preE7NonPairAction w U) ∈ N.1 ↔
    (e.1 : preE7NonPairAction w U) ∈ N.1
  simpa only [k, q,
    ElementaryMinimalNormalChart.quotientKernelEquiv_coe,
    C.equiv.symm_apply_apply]

/-- Maschke complement for the exact invariant intersection
`I = N ∩ E`.  Since `U/E` has order prime to five, the complement is an
actual `U/E`-subrepresentation of the correlated translation module.  If
the translation image survives modulo `N`, this complement is nonzero. -/
theorem degreeFive_translationNormalSpace_exists_nonzero_isCompl
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (hr : Nat.card block.Fibre = 5)
    (hs : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3)
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U))
    (hretained : ¬ E block P ≤ N.1) :
    let C := elementaryChart block P
    let A := C.quotientRepresentation
    let I := C.originalKernelChart.normalSubrepresentation
      (QuotientGroup.mk' (E block P))
      (QuotientGroup.mk'_surjective (E block P)) A N.1
    ∃ J : Subrepresentation A.ρ, IsCompl I J ∧ J ≠ ⊥ := by
  let C := elementaryChart block P
  let A := C.quotientRepresentation
  let q : preE7NonPairAction w U →*
      preE7NonPairAction w U ⧸ E block P :=
    QuotientGroup.mk' (E block P)
  let I := C.originalKernelChart.normalSubrepresentation
    q (QuotientGroup.mk'_surjective (E block P)) A N.1
  have hp : C.p = 5 := by
    change P.p = 5
    exact degreeFive_profilePrime_eq_five block P hr
  letI : NeZero
      (Nat.card (preE7NonPairAction w U ⧸ E block P) : ZMod C.p) := by
    constructor
    intro hzero
    have hdiv : C.p ∣ Nat.card
        (preE7NonPairAction w U ⧸ E block P) :=
      (ZMod.natCast_eq_zero_iff _ _).mp hzero
    rw [hp] at hdiv
    exact (Nat.prime_five.coprime_iff_not_dvd.mp
      (degreeFive_complementQuotient_coprime_five block P hr hs)) hdiv
  obtain ⟨J, hIJ⟩ := exists_isCompl I
  refine ⟨J, hIJ, ?_⟩
  intro hJ
  have hI : I = ⊤ := by
    have htop : I ⊔ J = ⊤ := hIJ.codisjoint.eq_top
    simpa only [hJ, sup_bot_eq] using htop
  apply hretained
  intro e he
  let k : q.ker := C.quotientKernelEquiv (C.equiv ⟨e, he⟩)
  have hkernel :
      (C.originalKernelChart.kernelCoordinates q A).ker ≤
        N.1.subgroupOf q.ker := by
    intro x hx
    have hx1 : x = 1 := by
      apply C.originalKernelChart.equiv.symm.injective
      exact (MonoidHom.mem_ker.mp hx).trans
        (map_one C.originalKernelChart.equiv.symm).symm
    subst x
    exact Subgroup.one_mem _
  have hkcoord :
      (C.originalKernelChart.kernelCoordinates q A k).toAdd =
        (C.equiv ⟨e, he⟩).toAdd := by
    change (C.equiv
      (C.equiv.symm (C.equiv ⟨e, he⟩))).toAdd = _
    rw [C.equiv.apply_symm_apply]
  have hkspace :
      (C.originalKernelChart.kernelCoordinates q A k).toAdd ∈
        C.originalKernelChart.normalSpace q A N.1 := by
    change (C.originalKernelChart.kernelCoordinates q A k).toAdd ∈ I
    rw [hI]
    exact Submodule.mem_top
  have hkN : k ∈ N.1.subgroupOf q.ker :=
    (sectionSubgroupImage_mem_iff
      (C.originalKernelChart.kernelCoordinates q A)
      (N.1.subgroupOf q.ker) hkernel k).mp hkspace
  change (k.1 : preE7NonPairAction w U) ∈ N.1 at hkN
  simpa only [k, q,
    ElementaryMinimalNormalChart.quotientKernelEquiv_coe,
    C.equiv.symm_apply_apply] using hkN

/-- A diagonal element of `R=U/E` which fixes a nonzero invariant
subspace of the actual correlated translation module is trivial.  Maschke
will supply precisely such a subspace for every retained quotient section.
The proof sees one nonzero vector at each block and then uses faithfulness
of the literal one-dimensional local affine action. -/
theorem degreeFiveQuotientBlockKernel_eq_one_of_fixes_nonzeroSubrepresentation
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (hr : Nat.card block.Fibre = 5)
    (J : Subrepresentation
      (elementaryChart block P).quotientRepresentation.ρ)
    (hJ : J ≠ ⊥)
    (d : degreeFiveQuotientBlockKernel block P)
    (hfix : ∀ v : (elementaryChart block P).V, v ∈ J →
      (elementaryChart block P).quotientRepresentation.ρ d.1 v = v) :
    d = 1 := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (E block P) d.1
  have hdTop : (quotientEmbedding block P d.1).right = 1 :=
    MonoidHom.mem_ker.mp d.2
  have hgRight : (ambientEmbedding block g).right = 1 := by
    rw [← hg] at hdTop
    exact hdTop
  have hgTop : block.topMap g = 1 := by
    simpa only [ambientEmbedding, ActualBlockWreathEmbedding.embedding]
      using congrArg Subtype.val hgRight
  have hleft : ∀ i : block.Points,
      (quotientEmbedding block P d.1).left i = 1 := by
    intro i
    obtain ⟨e, heJ, hecoord⟩ :=
      degreeFive_nonzeroSubrepresentation_coordinate_surjective_support
        block P J hJ i
    have hchart :
        ((elementaryChart block P).equiv
          (MulAut.conjNormal g e)).toAdd =
            ((elementaryChart block P).equiv e).toAdd := by
      rw [← (elementaryChart block P).quotientRepresentation_apply g e]
      rw [hg]
      exact hfix _ heJ
    have heconj : MulAut.conjNormal g e = e := by
      apply (elementaryChart block P).equiv.injective
      apply Multiplicative.toAdd.injective
      exact hchart
    have hcoordinate := degreeFive_coordinate_conjugation_of_top_fixed
      block P hTraceyPerm g e i (by rw [hgTop]; exact one_smul _ _)
    rw [heconj] at hcoordinate
    have hlocal :
        localMap block P ((ambientEmbedding block g).left i) = 1 :=
      degreeFiveLocalLinear_fixed_nonzero_eq_one block P hr _ _
        (by
          intro hz
          apply hecoord
          apply Multiplicative.toAdd.injective
          simpa only [hz, map_one, toAdd_one]) hcoordinate.symm
    rw [← hg]
    exact hlocal
  apply Subtype.ext
  change d.1 = (1 : preE7NonPairAction w U ⧸ E block P)
  apply quotientEmbedding_injective block P
  rw [map_one]
  apply PermutationalWreathProduct.ext
  · funext i
    simpa only [PermutationalWreathProduct.one_left] using hleft i
  · simpa only [PermutationalWreathProduct.one_right] using hdTop

/-- Full faithful-section theorem for every retained degree-five axis.
Maschke realizes the nonzero section `E/(E ∩ N)` as an invariant
complement in the original correlated translation module.  A block-kernel
element centralizing the retained section fixes that complement, so the
preceding literal coordinate theorem kills it in `U/E`. -/
theorem degreeFiveFaithfulTranslationSection_of_retained
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (hr : Nat.card block.Fibre = 5)
    (hs : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3)
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U))
    (hretained : ¬ E block P ≤ N.1) :
    DegreeFiveFaithfulTranslationSection block P N := by
  apply le_antisymm
  · rintro x ⟨hxCentral, hxBlock⟩
    obtain ⟨b, hbBlock, rfl⟩ := hxBlock
    let C := elementaryChart block P
    let A := C.quotientRepresentation
    let qE : preE7NonPairAction w U →*
        preE7NonPairAction w U ⧸ E block P :=
      QuotientGroup.mk' (E block P)
    let qN : preE7NonPairAction w U →*
        preE7NonPairAction w U ⧸ N.1 := QuotientGroup.mk' N.1
    let I := C.originalKernelChart.normalSubrepresentation
      qE (QuotientGroup.mk'_surjective (E block P)) A N.1
    obtain ⟨J, hIJ, hJ⟩ :=
      degreeFive_translationNormalSpace_exists_nonzero_isCompl
        block P hr hs N hretained
    let d : degreeFiveQuotientBlockKernel block P :=
      ⟨qE b, hbBlock⟩
    have hd : d = 1 :=
      degreeFiveQuotientBlockKernel_eq_one_of_fixes_nonzeroSubrepresentation
        hTraceyPerm block P hr J hJ d (by
          intro v hvJ
          obtain ⟨e, he⟩ := C.equiv.surjective (Multiplicative.ofAdd v)
          have heAdd : (C.equiv e).toAdd = v :=
            congrArg Multiplicative.toAdd he
          let k : E block P := MulAut.conjNormal b e * e⁻¹
          have heImage : qN e.1 ∈ degreeFiveTranslationImage block P N :=
            ⟨e.1, e.2, rfl⟩
          have hcomm : Commute (qN e.1) (qN b) :=
            Subgroup.mem_centralizer_iff.mp hxCentral (qN e.1) heImage
          have hkN : (k.1 : preE7NonPairAction w U) ∈ N.1 := by
            apply (QuotientGroup.eq_one_iff k.1).mp
            change qN (b * e.1 * b⁻¹ * e.1⁻¹) = 1
            simp only [map_mul, map_inv]
            rw [hcomm.eq.symm]
            simp
          have hkI : (C.equiv k).toAdd ∈ I := by
            exact (degreeFive_elementaryChart_mem_normalSubrepresentation_iff
              block P N k).2 hkN
          let av : C.V := A.ρ (qE b) (C.equiv e).toAdd
          have hconjJ : av ∈ J :=
            J.apply_mem_toSubmodule (qE b) (by simpa only [heAdd] using hvJ)
          have hkJ : (C.equiv k).toAdd ∈ J := by
            have haction := C.quotientRepresentation_apply b e
            have hsub :
                av - (C.equiv e).toAdd ∈ J :=
              J.toSubmodule.sub_mem hconjJ (by simpa only [heAdd] using hvJ)
            have hkcoord :
                (C.equiv k).toAdd =
                  av - (C.equiv e).toAdd := by
              dsimp only [av]
              change (C.equiv (MulAut.conjNormal b e * e⁻¹)).toAdd = _
              rw [map_mul, map_inv, toAdd_mul, toAdd_inv]
              simp only [sub_eq_add_neg]
              rw [← haction]
            rw [hkcoord]
            exact hsub
          have hkzero : (C.equiv k).toAdd = 0 := by
            exact (Submodule.mem_bot (R := ZMod C.p)).mp
              (hIJ.disjoint.le_bot ⟨hkI, hkJ⟩)
          have haction := C.quotientRepresentation_apply b e
          let av' : C.V := A.ρ (qE b) v
          have hdiff : av' - v = 0 := by
            dsimp only [av']
            rw [← heAdd, haction]
            have hkcoord :
                (C.equiv k).toAdd =
                  (C.equiv (MulAut.conjNormal b e)).toAdd -
                    (C.equiv e).toAdd := by
              change (C.equiv (MulAut.conjNormal b e * e⁻¹)).toAdd = _
              rw [map_mul, map_inv, toAdd_mul, toAdd_inv]
              simp only [sub_eq_add_neg]
            rw [← hkcoord, hkzero]
          exact sub_eq_zero.mp hdiff)
    have hbE : b ∈ E block P := by
      apply (QuotientGroup.eq_one_iff _).mp
      exact congrArg Subtype.val hd
    exact ⟨b, hbE, rfl⟩
  · intro x hx
    refine ⟨?_, degreeFiveTranslationImage_le_retainedBlockKernel
      block P N hx⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro y hy
    exact congrArg Subtype.val ((degreeFiveTranslationImage_commute
      block P N ⟨y, hy⟩ ⟨x, hx⟩).eq)

/-- The easy inclusion in the faithful-section identity: the retained
translation group is abelian and is contained in the block kernel. -/
theorem degreeFiveTranslationImage_le_centralizer_inf_retainedBlockKernel
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U)) :
    degreeFiveTranslationImage block P N ≤
      Subgroup.centralizer
          (degreeFiveTranslationImage block P N :
            Set (preE7NonPairAction w U ⧸ N.1)) ⊓
        degreeFiveRetainedBlockKernel block P N := by
  intro x hx
  refine ⟨?_, degreeFiveTranslationImage_le_retainedBlockKernel
    block P N hx⟩
  apply Subgroup.mem_centralizer_iff.mpr
  intro y hy
  exact congrArg Subtype.val
    ((degreeFiveTranslationImage_commute block P N ⟨y, hy⟩ ⟨x, hx⟩).eq)

/-- Under the faithful-section identity, any subgroup centralizing the
translation section and disjoint from it is disjoint from the whole
retained block kernel. -/
theorem degreeFive_centralizer_disjoint_retainedBlockKernel
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U))
    (H : Subgroup (preE7NonPairAction w U ⧸ N.1))
    (hfaithful : DegreeFiveFaithfulTranslationSection block P N)
    (hcentral : H ≤ Subgroup.centralizer
      (degreeFiveTranslationImage block P N :
        Set (preE7NonPairAction w U ⧸ N.1)))
    (hdisjoint : H ⊓ degreeFiveTranslationImage block P N = ⊥) :
    H ⊓ degreeFiveRetainedBlockKernel block P N = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have hxV : x ∈ degreeFiveTranslationImage block P N := by
    rw [← hfaithful]
    exact ⟨hcentral hx.1, hx.2⟩
  have hxInf : x ∈ H ⊓ degreeFiveTranslationImage block P N :=
    ⟨hx.1, hxV⟩
  rw [hdisjoint] at hxInf
  exact hxInf

/-- The exact top section retained after an arbitrary literal normal axis.
The target is kept as the original quotient `U/(B∨N)`, where `B` is the
actual block-kernel preimage. -/
def degreeFiveRetainedTopMap
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U)) :
    (preE7NonPairAction w U ⧸ N.1) →*
      preE7NonPairAction w U ⧸
        (degreeFiveBlockKernelPreimage block P ⊔ N.1) :=
  QuotientGroup.lift N.1
    (QuotientGroup.mk'
      (degreeFiveBlockKernelPreimage block P ⊔ N.1)) (by
        rw [QuotientGroup.ker_mk']
        exact le_sup_right)

@[simp] theorem degreeFiveRetainedTopMap_apply
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U))
    (g : preE7NonPairAction w U) :
    degreeFiveRetainedTopMap block P N (QuotientGroup.mk' N.1 g) =
      QuotientGroup.mk'
        (degreeFiveBlockKernelPreimage block P ⊔ N.1) g :=
  rfl

theorem degreeFiveRetainedTopMap_surjective
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U)) :
    Function.Surjective (degreeFiveRetainedTopMap block P N) := by
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
    (degreeFiveBlockKernelPreimage block P ⊔ N.1) q
  exact ⟨QuotientGroup.mk' N.1 g, rfl⟩

/-- Its kernel is exactly the retained image of the block kernel. -/
theorem degreeFiveRetainedTopMap_ker
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U)) :
    (degreeFiveRetainedTopMap block P N).ker =
      degreeFiveRetainedBlockKernel block P N := by
  rw [degreeFiveRetainedTopMap, QuotientGroup.ker_lift,
    QuotientGroup.ker_mk', Subgroup.map_sup,
    QuotientGroup.map_mk'_self, sup_bot_eq]

/-- Restriction of the literal retained top projection to a selected
ambient subgroup. -/
def degreeFiveRestrictedRetainedTopMap
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U))
    (H : Subgroup (preE7NonPairAction w U ⧸ N.1)) :
    H →* preE7NonPairAction w U ⧸
      (degreeFiveBlockKernelPreimage block P ⊔ N.1) :=
  (degreeFiveRetainedTopMap block P N).comp H.subtype

/-- A subgroup disjoint from the retained block kernel embeds in the exact
retained top section. -/
theorem degreeFiveRestrictedRetainedTopMap_injective_of_disjoint
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U))
    (H : Subgroup (preE7NonPairAction w U ⧸ N.1))
    (hdisjoint : H ⊓ degreeFiveRetainedBlockKernel block P N = ⊥) :
    Function.Injective
      (degreeFiveRestrictedRetainedTopMap block P N H) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_antisymm
  · intro x hx
    have hxB : (x.1 : preE7NonPairAction w U ⧸ N.1) ∈
        degreeFiveRetainedBlockKernel block P N := by
      rw [← degreeFiveRetainedTopMap_ker block P N]
      exact MonoidHom.mem_ker.mp hx
    have hxInf : (x.1 : preE7NonPairAction w U ⧸ N.1) ∈
        H ⊓ degreeFiveRetainedBlockKernel block P N := ⟨x.2, hxB⟩
    rw [hdisjoint] at hxInf
    exact Subtype.ext (Subgroup.mem_bot.mp hxInf)
  · exact bot_le

/-- The top projection is onto the literal transitive block group. -/
theorem degreeFiveQuotientTopMap_surjective
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre] :
    Function.Surjective (degreeFiveQuotientTopMap block P) := by
  intro q
  obtain ⟨g, hg⟩ := q.2
  refine ⟨QuotientGroup.mk' (E block P) g, ?_⟩
  change (block.topMap.rangeRestrict g : block.Top) = q
  exact Subtype.ext hg

/-- The same top projection on the original ambient action. -/
def degreeFiveOriginalTopMap
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre] :
    preE7NonPairAction w U →* block.Top :=
  (degreeFiveQuotientTopMap block P).comp
    (QuotientGroup.mk' (E block P))

theorem degreeFiveOriginalTopMap_surjective
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre] :
    Function.Surjective (degreeFiveOriginalTopMap block P) :=
  (degreeFiveQuotientTopMap_surjective block P).comp
    (QuotientGroup.mk'_surjective (E block P))

theorem degreeFiveOriginalTopMap_ker
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre] :
    (degreeFiveOriginalTopMap block P).ker =
      degreeFiveBlockKernelPreimage block P := by
  rfl

/-- The literal image of every retained axis in the block top is normal.
This is the exact instance required to form the corresponding quotient of
the actual top. -/
instance degreeFiveRetainedTopAxisImage_normal
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U)) :
    ((degreeFiveBlockKernelPreimage block P ⊔ N.1).map
      (degreeFiveOriginalTopMap block P)).Normal :=
  Subgroup.Normal.map inferInstance (degreeFiveOriginalTopMap block P)
    (degreeFiveOriginalTopMap_surjective block P)

/-- Identify the retained top section with a quotient of the literal
transitive block top. -/
noncomputable def degreeFiveRetainedTopEquiv
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U)) :
    (preE7NonPairAction w U ⧸
        (degreeFiveBlockKernelPreimage block P ⊔ N.1)) ≃*
      (block.Top ⧸
        (degreeFiveBlockKernelPreimage block P ⊔ N.1).map
          (degreeFiveOriginalTopMap block P)) :=
  quotientEquivOfKerLe (degreeFiveOriginalTopMap block P)
    (degreeFiveOriginalTopMap_surjective block P)
    (degreeFiveBlockKernelPreimage block P ⊔ N.1) (by
      rw [degreeFiveOriginalTopMap_ker block P]
      exact le_sup_left)

/-- Every subgroup of the actual block top has the published all-prime
permutation sectional-rank bound. -/
theorem degreeFiveBlockTop_primeSectionalRank
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (p : ℕ) [Fact p.Prime] :
    PrimeSectionalRankBound p block.Top
      (Nat.card block.Points / p) := by
  intro K
  simpa only [Fintype.card_eq_nat_card] using
    (permutation_primeCharacterRank_le p K block.Points)

/-- The retained top is a quotient section of the literal block top, so
the same sharp sectional prime bound survives every normal axis. -/
theorem degreeFiveRetainedTop_primeSectionalRank
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (p : ℕ) [Fact p.Prime]
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U)) :
    PrimeSectionalRankBound p
      (preE7NonPairAction w U ⧸
        (degreeFiveBlockKernelPreimage block P ⊔ N.1))
      (Nat.card block.Points / p) := by
  let L : Subgroup block.Top :=
    (degreeFiveBlockKernelPreimage block P ⊔ N.1).map
      (degreeFiveOriginalTopMap block P)
  have hquot : PrimeSectionalRankBound p (block.Top ⧸ L)
      (Nat.card block.Points / p) :=
    PrimeSectionalRankBound.of_surjective p
      (degreeFiveBlockTop_primeSectionalRank block p)
      (QuotientGroup.mk' L) (QuotientGroup.mk'_surjective L)
  exact PrimeSectionalRankBound.of_injective p hquot
    (degreeFiveRetainedTopEquiv block P N).toMonoidHom
    (degreeFiveRetainedTopEquiv block P N).injective

/-- Any subgroup disjoint from the retained block kernel inherits the
sharp prime-character bound from the exact top section. -/
theorem degreeFiveRetainedBlockKernelDisjoint_primeCharacterRank_le
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (p : ℕ) [Fact p.Prime]
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U))
    (H : Subgroup (preE7NonPairAction w U ⧸ N.1))
    (hdisjoint : H ⊓ degreeFiveRetainedBlockKernel block P N = ⊥) :
    Module.finrank (ZMod p) (PrimeCharacters p H) ≤
      Nat.card block.Points / p := by
  let f := degreeFiveRestrictedRetainedTopMap block P N H
  exact primeCharacterRank_le_of_injective p
    (degreeFiveRetainedTop_primeSectionalRank block P p N) f
    (degreeFiveRestrictedRetainedTopMap_injective_of_disjoint
      block P N H hdisjoint)

/-- Once the literal faithful-section identity is known, every outer
prime-primary socle part is disjoint from the complete retained block
kernel. -/
theorem degreeFiveOuterPrimeSoclePart_inf_retainedBlockKernel
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (hr : Nat.card block.Fibre = 5)
    (hs : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3)
    (p : ℕ) [Fact p.Prime]
    (hp5 : Nat.Coprime p 5)
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U))
    (hfaithful : DegreeFiveFaithfulTranslationSection block P N) :
    degreeFiveOuterPrimeSoclePart p N ⊓
      degreeFiveRetainedBlockKernel block P N = ⊥ := by
  apply degreeFive_centralizer_disjoint_retainedBlockKernel
    block P N (degreeFiveOuterPrimeSoclePart p N) hfaithful
  · exact (degreeFiveOuterPrimeSoclePart_le_outer p N).trans
      (degreeFiveOuterSoclePart_le_translationCentralizer
        block P hr hs N)
  · exact degreeFiveOuterPrimeSoclePart_inf_translationImage
      block P hr p hp5 N

/-- Sharp top-section normal-generator bound for each non-five outer prime
type. -/
theorem degreeFiveOuterPrimeSoclePart_normalGen_le
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (hr : Nat.card block.Fibre = 5)
    (hs : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3)
    (p : ℕ) [Fact p.Prime]
    (hp5 : Nat.Coprime p 5)
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U))
    (hfaithful : DegreeFiveFaithfulTranslationSection block P N) :
    MarkedC4.normalGen (degreeFiveOuterPrimeSoclePart p N) ≤
      Nat.card block.Points / p := by
  exact (MarkedC4.normalGen_normalSubgroup_le_primeCharacterRank p
      (degreeFiveOuterPrimeSoclePart p N)
      (degreeFiveOuterPrimeSoclePart_isPGroup p N)).trans
    (degreeFiveRetainedBlockKernelDisjoint_primeCharacterRank_le
      block P p N (degreeFiveOuterPrimeSoclePart p N)
      (degreeFiveOuterPrimeSoclePart_inf_retainedBlockKernel
        block P hr hs p hp5 N hfaithful))

/-- Restriction of the actual block-top projection to a subgroup. -/
def degreeFiveRestrictedTopMap
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (H : Subgroup (preE7NonPairAction w U ⧸ E block P)) :
    H →* block.Top :=
  (degreeFiveQuotientTopMap block P).comp H.subtype

/-- Any subgroup disjoint from the actual diagonal block kernel embeds in
the actual top. -/
theorem degreeFiveRestrictedTopMap_injective_of_disjoint
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (H : Subgroup (preE7NonPairAction w U ⧸ E block P))
    (hdisjoint : H ⊓ degreeFiveQuotientBlockKernel block P = ⊥) :
    Function.Injective (degreeFiveRestrictedTopMap block P H) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_antisymm
  · intro x hx
    have hxInf : (x.1 : preE7NonPairAction w U ⧸ E block P) ∈
        H ⊓ degreeFiveQuotientBlockKernel block P :=
      ⟨x.2, MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hx)⟩
    rw [hdisjoint] at hxInf
    exact Subtype.ext (Subgroup.mem_bot.mp hxInf)
  · exact bot_le

/-- The actual diagonal block kernel has order at most `4^s`. -/
theorem degreeFiveQuotientBlockKernel_card_le
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (hr : Nat.card block.Fibre = 5) :
    Nat.card (degreeFiveQuotientBlockKernel block P) ≤
      4 ^ Nat.card block.Points := by
  let f : degreeFiveQuotientBlockKernel block P →
      block.Points → LocalQuotient block P :=
    fun x ↦ (quotientEmbedding block P x.1).left
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply quotientEmbedding_injective block P
    apply PermutationalWreathProduct.ext
    · exact hxy
    · have hx : (quotientEmbedding block P x.1).right = 1 :=
        MonoidHom.mem_ker.mp x.2
      have hy : (quotientEmbedding block P y.1).right = 1 :=
        MonoidHom.mem_ker.mp y.2
      exact hx.trans hy.symm
  have hlocal : Nat.card (LocalQuotient block P) ≤ 4 :=
    Nat.le_of_dvd (by norm_num)
      (degreeFive_localQuotient_card_dvd_four block P hr)
  calc
    Nat.card (degreeFiveQuotientBlockKernel block P) ≤
        Nat.card (block.Points → LocalQuotient block P) :=
      Nat.card_le_card_of_injective f hf
    _ = Nat.card (LocalQuotient block P) ^ Nat.card block.Points :=
      Nat.card_fun
    _ ≤ 4 ^ Nat.card block.Points :=
      Nat.pow_le_pow_left hlocal _

/-- The literal diagonal block kernel is abelian, since it lies in the
product of the actual cyclic local complements. -/
theorem degreeFiveQuotientBlockKernel_commute
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (hr : Nat.card block.Fibre = 5)
    (x y : degreeFiveQuotientBlockKernel block P) : Commute x y := by
  letI : IsCyclic (LocalQuotient block P) :=
    degreeFive_localQuotient_isCyclic block P hr
  letI : CommGroup (LocalQuotient block P) := IsCyclic.commGroup
  rw [Commute]
  apply Subtype.ext
  apply quotientEmbedding_injective block P
  apply PermutationalWreathProduct.ext
  · funext i
    have hx : (quotientEmbedding block P x.1).right = 1 :=
      MonoidHom.mem_ker.mp x.2
    have hy : (quotientEmbedding block P y.1).right = 1 :=
      MonoidHom.mem_ker.mp y.2
    change (quotientEmbedding block P (x.1 * y.1)).left i =
      (quotientEmbedding block P (y.1 * x.1)).left i
    rw [map_mul, map_mul, PermutationalWreathProduct.mul_left,
      PermutationalWreathProduct.mul_left, hx, hy]
    simp only [inv_one, one_smul]
    exact mul_comm
      ((quotientEmbedding block P x.1).left i)
      ((quotientEmbedding block P y.1).left i)
  · change (quotientEmbedding block P (x.1 * y.1)).right =
      (quotientEmbedding block P (y.1 * x.1)).right
    rw [map_mul, map_mul, PermutationalWreathProduct.mul_right,
      PermutationalWreathProduct.mul_right]
    have hx : (quotientEmbedding block P x.1).right = 1 :=
      MonoidHom.mem_ker.mp x.2
    have hy : (quotientEmbedding block P y.1).right = 1 :=
      MonoidHom.mem_ker.mp y.2
    rw [hx, hy]

/-- The actual diagonal kernel is an abelian group, not merely a subgroup
of one abstractly isomorphic to an abelian group. -/
theorem degreeFiveQuotientBlockKernel_isMulCommutative
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (hr : Nat.card block.Fibre = 5) :
    IsMulCommutative (degreeFiveQuotientBlockKernel block P) :=
  IsMulCommutative.of_comm fun x y =>
    (degreeFiveQuotientBlockKernel_commute block P hr x y).eq

/-- The literal faithful top in a two-block residual frame has order two. -/
theorem degreeFive_top_card_eq_two
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (hs : Nat.card block.Points = 2) : Nat.card block.Top = 2 := by
  letI : MulAction.IsPretransitive block.Top block.Points :=
    block.top_pretransitive
  letI : Finite block.Top := block.top_finite
  have hUpper : Nat.card block.Top ≤ 2 := by
    calc
      Nat.card block.Top ≤ Nat.card (Equiv.Perm block.Points) :=
        Nat.card_le_card_of_injective block.Top.subtype Subtype.val_injective
      _ = (Nat.card block.Points).factorial := Nat.card_perm
      _ = 2 := by rw [hs]; norm_num
  have hIndex : (MulAction.stabilizer block.Top block.base).index = 2 := by
    simpa only [hs] using
      MulAction.index_stabilizer_of_transitive block.Top block.base
  have hMul := (MulAction.stabilizer block.Top block.base).card_mul_index
  rw [hIndex] at hMul
  have hPositive : 0 < Nat.card (MulAction.stabilizer block.Top block.base) :=
    Nat.card_pos
  omega

/-- The literal faithful top in a three-block residual frame has order
three or six.  This is just orbit--stabilizer inside the actual `S₃`. -/
theorem degreeFive_top_card_eq_three_or_six
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (hs : Nat.card block.Points = 3) :
    Nat.card block.Top = 3 ∨ Nat.card block.Top = 6 := by
  letI : MulAction.IsPretransitive block.Top block.Points :=
    block.top_pretransitive
  letI : Finite block.Top := block.top_finite
  have hUpper : Nat.card block.Top ≤ 6 := by
    calc
      Nat.card block.Top ≤ Nat.card (Equiv.Perm block.Points) :=
        Nat.card_le_card_of_injective block.Top.subtype Subtype.val_injective
      _ = (Nat.card block.Points).factorial := Nat.card_perm
      _ = 6 := by rw [hs]; norm_num
  have hIndex : (MulAction.stabilizer block.Top block.base).index = 3 := by
    simpa only [hs] using
      MulAction.index_stabilizer_of_transitive block.Top block.base
  have hMul := (MulAction.stabilizer block.Top block.base).card_mul_index
  rw [hIndex] at hMul
  have hPositive : 0 < Nat.card (MulAction.stabilizer block.Top block.base) :=
    Nat.card_pos
  omega

/-- Relabel the actual top on three blocks without changing the group. -/
def degreeFiveTopRelabel
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (points : block.Points ≃ Fin 3) :
    block.Top →* Equiv.Perm (Fin 3) :=
  points.permCongrHom.toMonoidHom.comp block.Top.subtype

theorem degreeFiveTopRelabel_injective
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (points : block.Points ≃ Fin 3) :
    Function.Injective (degreeFiveTopRelabel block points) :=
  points.permCongrHom.injective.comp Subtype.val_injective

/-- The one finite fact about the full three-point symmetric group used by
the degree-five source.  The kernel verifies the complete multiplication
table, so this is not a project assumption or a catalogue lookup. -/
private theorem finThree_firstDerived_card_eq_three :
    Nat.card (derivedSeries (Equiv.Perm (Fin 3)) 1) = 3 := by
  have heq : derivedSeries (Equiv.Perm (Fin 3)) 1 = NaturalS4.a3 := by
    apply le_antisymm
    · rw [derivedSeries_succ, derivedSeries_zero, Subgroup.commutator_le]
      intro a _ b _
      exact NaturalS4.commutator_mem_a3Set a b
    · intro x hx
      change x ∈ NaturalS4.a3Set at hx
      simp only [NaturalS4.a3Set, Finset.mem_insert,
        Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact Subgroup.one_mem _
      · have hcomm :
            (Equiv.swap 0 1 : Equiv.Perm (Fin 3)) * Equiv.swap 1 2 =
              ⁅(Equiv.swap 1 2 : Equiv.Perm (Fin 3)), Equiv.swap 0 1⁆ := by
          decide
        rw [hcomm]
        exact NaturalS4.mem_derivedSeries_one _ _
      · have hcomm :
            (Equiv.swap 1 2 : Equiv.Perm (Fin 3)) * Equiv.swap 0 1 =
              ⁅(Equiv.swap 0 1 : Equiv.Perm (Fin 3)), Equiv.swap 1 2⁆ := by
          decide
        rw [hcomm]
        exact NaturalS4.mem_derivedSeries_one _ _
  rw [heq]
  rw [show Nat.card NaturalS4.a3 =
      Nat.card {σ // σ ∈ NaturalS4.a3Set} from rfl,
    Nat.card_eq_finsetCard]
  decide

private theorem finTwo_secondDerived_eq_bot :
    derivedSeries (Equiv.Perm (Fin 2)) 2 = ⊥ := by
  rw [show 2 = 1 + 1 by norm_num, derivedSeries_succ, eq_bot_iff,
    Subgroup.commutator_le]
  intro a _ b _
  rw [commutatorElement_eq_one_iff_mul_comm.mpr
    (AnnihilatorYonedaFixture.perm_two_comm a b)]
  exact Subgroup.one_mem _

private theorem finThree_secondDerived_eq_bot :
    derivedSeries (Equiv.Perm (Fin 3)) 2 = ⊥ := by
  exact NaturalS4.derivedSeries_S3_two

/-- Every literal two- or three-block top has derived length at most two.
This is checked only in `S₂` and `S₃`; the actual top is transported by
its faithful relabelling. -/
theorem degreeFive_top_secondDerived_eq_bot
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (hs : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3) :
    derivedSeries block.Top 2 = ⊥ := by
  rcases hs with hs | hs
  · let points : block.Points ≃ Fin 2 := Finite.equivFinOfCardEq hs
    let f : block.Top →* Equiv.Perm (Fin 2) :=
      points.permCongrHom.toMonoidHom.comp block.Top.subtype
    have hf : Function.Injective f :=
      points.permCongrHom.injective.comp Subtype.val_injective
    apply le_antisymm
    · intro x hx
      have himage : f x ∈ derivedSeries (Equiv.Perm (Fin 2)) 2 :=
        map_derivedSeries_le_derivedSeries f 2 ⟨x, hx, rfl⟩
      rw [finTwo_secondDerived_eq_bot] at himage
      exact Subgroup.mem_bot.mpr
        (hf ((Subgroup.mem_bot.mp himage).trans (map_one f).symm))
    · exact bot_le
  · let points : block.Points ≃ Fin 3 := Finite.equivFinOfCardEq hs
    let f := degreeFiveTopRelabel block points
    have hf := degreeFiveTopRelabel_injective block points
    apply le_antisymm
    · intro x hx
      have himage : f x ∈ derivedSeries (Equiv.Perm (Fin 3)) 2 :=
        map_derivedSeries_le_derivedSeries f 2 ⟨x, hx, rfl⟩
      rw [finThree_secondDerived_eq_bot] at himage
      exact Subgroup.mem_bot.mpr
        (hf ((Subgroup.mem_bot.mp himage).trans (map_one f).symm))
    · exact bot_le

/-- Every retained top quotient still has derived length at most two.  The
statement is kept on the literal quotient `U/(B ⊔ N)` used by the retained
axis; its identification with a quotient of the actual block top is the
proved equivalence `degreeFiveRetainedTopEquiv`. -/
theorem degreeFiveRetainedTop_secondDerived_eq_bot
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (hs : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3)
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U)) :
    derivedSeries
        (preE7NonPairAction w U ⧸
          (degreeFiveBlockKernelPreimage block P ⊔ N.1)) 2 = ⊥ := by
  let L : Subgroup block.Top :=
    (degreeFiveBlockKernelPreimage block P ⊔ N.1).map
      (degreeFiveOriginalTopMap block P)
  have hquot : derivedSeries (block.Top ⧸ L) 2 = ⊥ := by
    rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective L) 2,
      degreeFive_top_secondDerived_eq_bot block hs, Subgroup.map_bot]
  let e := degreeFiveRetainedTopEquiv block P N
  apply le_antisymm
  · intro x hx
    have hxmap : e x ∈ derivedSeries (block.Top ⧸ L) 2 :=
      map_derivedSeries_le_derivedSeries e.toMonoidHom 2 ⟨x, hx, rfl⟩
    rw [hquot] at hxmap
    exact Subgroup.mem_bot.mpr
      (e.injective ((Subgroup.mem_bot.mp hxmap).trans
        (map_one e.toMonoidHom).symm))
  · exact bot_le

/-- The literal retained top has order dividing the order of the actual
two- or three-block top. -/
theorem degreeFiveRetainedTop_card_dvd_top
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U)) :
    Nat.card
        (preE7NonPairAction w U ⧸
          (degreeFiveBlockKernelPreimage block P ⊔ N.1)) ∣
      Nat.card block.Top := by
  let L : Subgroup block.Top :=
    (degreeFiveBlockKernelPreimage block P ⊔ N.1).map
      (degreeFiveOriginalTopMap block P)
  have hcard : Nat.card
      (preE7NonPairAction w U ⧸
        (degreeFiveBlockKernelPreimage block P ⊔ N.1)) =
      Nat.card (block.Top ⧸ L) :=
    Nat.card_congr (degreeFiveRetainedTopEquiv block P N).toEquiv
  rw [hcard]
  exact Subgroup.card_dvd_of_surjective (QuotientGroup.mk' L)
    (QuotientGroup.mk'_surjective L)

/-- A subgroup disjoint from the retained block kernel has second derived
subgroup zero, because it injects into the literal retained top. -/
theorem degreeFiveRetainedBlockKernelDisjoint_secondDerived_eq_bot
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (hs : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3)
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U))
    (H : Subgroup (preE7NonPairAction w U ⧸ N.1))
    (hdisjoint : H ⊓ degreeFiveRetainedBlockKernel block P N = ⊥) :
    derivedSeries H 2 = ⊥ := by
  let f := degreeFiveRestrictedRetainedTopMap block P N H
  have hf : Function.Injective f :=
    degreeFiveRestrictedRetainedTopMap_injective_of_disjoint
      block P N H hdisjoint
  apply le_antisymm
  · intro x hx
    have hxmap : f x ∈ derivedSeries
        (preE7NonPairAction w U ⧸
          (degreeFiveBlockKernelPreimage block P ⊔ N.1)) 2 :=
      map_derivedSeries_le_derivedSeries f 2 ⟨x, hx, rfl⟩
    rw [degreeFiveRetainedTop_secondDerived_eq_bot block P hs N] at hxmap
    exact Subgroup.mem_bot.mpr
      (hf ((Subgroup.mem_bot.mp hxmap).trans (map_one f).symm))
  · exact bot_le

/-- Under the literal faithful-section identity an outer ambient minimal
normal factor is abelian.  Indeed it embeds in a two-step-solvable retained
top, while a nonabelian minimal normal subgroup is perfect. -/
theorem degreeFiveOuterMinimal_isMulCommutative
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (hr : Nat.card block.Fibre = 5)
    (hs : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3)
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U))
    (M : Subgroup (preE7NonPairAction w U ⧸ N.1))
    (hM : IsMinimalNormalSubgroup M)
    (houter : ¬ IsPGroup 5 M)
    (hfaithful : DegreeFiveFaithfulTranslationSection block P N) :
    IsMulCommutative M := by
  have hdisjoint : M ⊓ degreeFiveRetainedBlockKernel block P N = ⊥ :=
    degreeFive_centralizer_disjoint_retainedBlockKernel
      block P N M hfaithful
        (degreeFiveOuterMinimal_le_translationCentralizer
          block P hr hs N M hM houter)
        (degreeFiveOuterMinimal_inf_translationImage
          block P hr hs N M hM houter)
  have hderived : derivedSeries M 2 = ⊥ :=
    degreeFiveRetainedBlockKernelDisjoint_secondDerived_eq_bot
      block P hs N M hdisjoint
  by_contra hnoncomm
  letI : M.Normal := hM.1
  letI : Group.IsPerfect M :=
    nonabelian_minimal_normal_perfect M (fun K hK hKM => by
      by_cases hKbot : K = ⊥
      · exact Or.inl hKbot
      · exact Or.inr (hM.2.2 K hK hKbot hKM)) hnoncomm
  have htop : derivedSeries M 2 = ⊤ := by
    have hfirst : derivedSeries M 1 = ⊤ := by
      rw [derivedSeries_one]
      exact Group.IsPerfect.commutator_eq_top
    rw [show 2 = 1 + 1 by norm_num, derivedSeries_succ, hfirst]
    exact Group.IsPerfect.commutator_eq_top
  have htopbot : (⊤ : Subgroup M) = ⊥ := htop.symm.trans hderived
  apply hM.2.1
  apply le_bot_iff.mp
  intro x hx
  let y : M := ⟨x, hx⟩
  have hy : y ∈ (⊥ : Subgroup M) := by
    rw [← htopbot]
    exact Subgroup.mem_top y
  exact Subgroup.mem_bot.mpr
    (congrArg Subtype.val (Subgroup.mem_bot.mp hy))

/-- Every outer minimal factor is elementary of prime two or three.  The
prime is read from the intrinsic elementary chart and forced by the
faithful embedding into the actual two- or three-block top. -/
theorem degreeFiveOuterMinimal_isPGroup_two_or_three
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (hr : Nat.card block.Fibre = 5)
    (hs : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3)
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U))
    (M : Subgroup (preE7NonPairAction w U ⧸ N.1))
    (hM : IsMinimalNormalSubgroup M)
    (houter : ¬ IsPGroup 5 M)
    (hfaithful : DegreeFiveFaithfulTranslationSection block P N) :
    IsPGroup 2 M ∨ IsPGroup 3 M := by
  letI : M.Normal := hM.1
  have hcomm : IsMulCommutative M :=
    degreeFiveOuterMinimal_isMulCommutative
      block P hr hs N M hM houter hfaithful
  let C := Classical.choice (elementaryMinimalNormalChart_nonempty M
    hM.2.1 hcomm (fun K hK hKM => by
      by_cases hKbot : K = ⊥
      · exact Or.inl hKbot
      · exact Or.inr (hM.2.2 K hK hKbot hKM)))
  letI : Finite C.V := Module.finite_of_finite (ZMod C.p)
  have hcard : Nat.card M =
      C.p ^ Module.finrank (ZMod C.p) C.V := by
    calc
      Nat.card M = Nat.card (Multiplicative C.V) :=
        Nat.card_congr C.equiv.toEquiv
      _ = Nat.card C.V := rfl
      _ = C.p ^ Module.finrank (ZMod C.p) C.V := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod C.p), Nat.card_zmod]
  have hcard_ne_one : Nat.card M ≠ 1 := by
    intro hone
    apply hM.2.1
    rw [← Subgroup.card_eq_one]
    exact hone
  have hdpos : 0 < Module.finrank (ZMod C.p) C.V := by
    by_contra hnot
    have hdzero : Module.finrank (ZMod C.p) C.V = 0 :=
      Nat.eq_zero_of_not_pos hnot
    apply hcard_ne_one
    rw [hcard, hdzero, pow_zero]
  have hdisjoint : M ⊓ degreeFiveRetainedBlockKernel block P N = ⊥ :=
    degreeFive_centralizer_disjoint_retainedBlockKernel
      block P N M hfaithful
        (degreeFiveOuterMinimal_le_translationCentralizer
          block P hr hs N M hM houter)
        (degreeFiveOuterMinimal_inf_translationImage
          block P hr hs N M hM houter)
  let f := degreeFiveRestrictedRetainedTopMap block P N M
  have hf : Function.Injective f :=
    degreeFiveRestrictedRetainedTopMap_injective_of_disjoint
      block P N M hdisjoint
  have hMtop : Nat.card M ∣ Nat.card block.Top :=
    (Subgroup.card_dvd_of_injective f hf).trans
      (degreeFiveRetainedTop_card_dvd_top block P N)
  have hpM : C.p ∣ Nat.card M := by
    rw [hcard]
    exact dvd_pow_self C.p hdpos.ne'
  have hpTop : C.p ∣ Nat.card block.Top := hpM.trans hMtop
  have finish (p : ℕ) (hp : C.p = p) : IsPGroup p M := by
    apply IsPGroup.of_card
    simpa only [hp] using hcard
  rcases hs with hs | hs
  · have htop : Nat.card block.Top = 2 :=
      degreeFive_top_card_eq_two block hs
    have hp2 : C.p ∣ 2 := by simpa only [htop] using hpTop
    have hp : C.p = 2 :=
      ((Nat.dvd_prime Nat.prime_two).mp hp2).resolve_left C.p_prime.ne_one
    exact Or.inl (finish 2 hp)
  · rcases degreeFive_top_card_eq_three_or_six block hs with htop | htop
    · have hp3 : C.p ∣ 3 := by simpa only [htop] using hpTop
      have hp : C.p = 3 :=
        ((Nat.dvd_prime Nat.prime_three).mp hp3).resolve_left C.p_prime.ne_one
      exact Or.inr (finish 3 hp)
    · have hp6 : C.p ∣ 2 * 3 := by
        simpa only [show 2 * 3 = 6 by norm_num, htop] using hpTop
      rcases C.p_prime.dvd_mul.mp hp6 with hp2 | hp3
      · have hp : C.p = 2 :=
          ((Nat.dvd_prime Nat.prime_two).mp hp2).resolve_left C.p_prime.ne_one
        exact Or.inl (finish 2 hp)
      · have hp : C.p = 3 :=
          ((Nat.dvd_prime Nat.prime_three).mp hp3).resolve_left C.p_prime.ne_one
        exact Or.inr (finish 3 hp)

/-- The outer part contains only the two prime types forced by the actual
block top.  Predicate-relative max sharing therefore bounds the entire
outer part by one normal generator. -/
theorem degreeFiveOuterSoclePart_normalGen_le_one
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (hr : Nat.card block.Fibre = 5)
    (hs : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3)
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U))
    (hfaithful : DegreeFiveFaithfulTranslationSection block P N) :
    MarkedC4.normalGen (degreeFiveOuterSoclePart N) ≤ 1 := by
  let Q := preE7NonPairAction w U ⧸ N.1
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hsplit := normalGen_minimalNormalSoclePart_le_max_primePrimaryParts
    2 Q (fun M ↦ ¬ IsPGroup 5 M)
  have hcomp : minimalNormalSoclePart Q
        (fun M ↦ ¬ IsPGroup 5 M ∧ ¬ IsPGroup 2 M) =
      degreeFiveOuterPrimeSoclePart 3 N := by
    apply minimalNormalSoclePart_congr
    intro M hM
    constructor
    · rintro ⟨hfive, htwo⟩
      refine ⟨hfive, ?_⟩
      rcases degreeFiveOuterMinimal_isPGroup_two_or_three
          block P hr hs N M hM hfive hfaithful with hp2 | hp3
      · exact False.elim (htwo hp2)
      · exact hp3
    · rintro ⟨hfive, hthree⟩
      refine ⟨hfive, ?_⟩
      intro htwo
      apply hM.2.1
      simpa only [inf_idem] using
        (isPGroup_inf_eq_bot_of_coprime 2 3 (by norm_num) M M htwo hthree)
  rw [hcomp] at hsplit
  apply hsplit.trans
  apply max_le
  · exact (degreeFiveOuterPrimeSoclePart_normalGen_le
      block P hr hs 2 (by norm_num) N hfaithful).trans (by
        rcases hs with hs | hs <;> rw [hs] <;> norm_num)
  · exact (degreeFiveOuterPrimeSoclePart_normalGen_le
      block P hr hs 3 (by norm_num) N hfaithful).trans (by
        rcases hs with hs | hs <;> rw [hs] <;> norm_num)

/-- Complete degree-five whole-socle generator theorem.  The translation
type is supplied by Tracey's published induced-module estimate; the outer
types use only the actual faithful section and the two- or three-block top. -/
theorem degreeFive_socle_normalGen_le_one
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (hr : Nat.card block.Fibre = 5)
    (hs : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3)
    (i₀ : block.Points)
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U))
    (hfaithful : DegreeFiveFaithfulTranslationSection block P N) :
    MarkedC4.normalGen
      (finiteGroupSocle (preE7NonPairAction w U ⧸ N.1)) ≤ 1 :=
  degreeFive_socle_normalGen_le_one_of_parts block P hr hs N
    (degreeFiveTranslationSoclePart_normalGen_le_one
      hTraceyHalf hTraceyPerm block P hr hs i₀ N)
    (degreeFiveOuterSoclePart_normalGen_le_one
      block P hr hs N hfaithful)

/-- Padded tuple exported to the degree-five complete-character interval. -/
noncomputable def degreeFive_socleNormalGeneratorBound
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (hr : Nat.card block.Fibre = 5)
    (hs : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3)
    (i₀ : block.Points)
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U))
    (hfaithful : DegreeFiveFaithfulTranslationSection block P N) :
    SocleNormalGeneratorBound (preE7NonPairAction w U ⧸ N.1) 1 :=
  (socleNormalGeneratorBound_iff_normalGen_le _ _).2
    (degreeFive_socle_normalGen_le_one hTraceyHalf hTraceyPerm
      block P hr hs i₀ N hfaithful)

/-- Unconditional construction-facing degree-five tuple on every retained
axis.  The faithful translation section is now a theorem of the actual
frame, rather than caller-supplied structure. -/
noncomputable def degreeFive_socleNormalGeneratorBound_of_retained
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (hr : Nat.card block.Fibre = 5)
    (hs : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3)
    (i₀ : block.Points)
    (N : DegreeFiveLiteralNormalAxis (w := w) (U := U))
    (hretained : ¬ E block P ≤ N.1) :
    SocleNormalGeneratorBound (preE7NonPairAction w U ⧸ N.1) 1 :=
  degreeFive_socleNormalGeneratorBound hTraceyHalf hTraceyPerm
    block P hr hs i₀ N
      (degreeFiveFaithfulTranslationSection_of_retained
        hTraceyPerm block P hr hs N hretained)

/-- The complete degree-five socle-generator menu required by the Zmud
interval constructor. -/
noncomputable def degreeFive_retainedSocleGeneratorMenu
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (hr : Nat.card block.Fibre = 5)
    (hs : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3)
    (i₀ : block.Points) :
    ∀ N : DegreeFiveLiteralNormalAxis (w := w) (U := U),
      ¬ E block P ≤ N.1 →
        SocleNormalGeneratorBound (preE7NonPairAction w U ⧸ N.1) 1 :=
  fun N hretained ↦ degreeFive_socleNormalGeneratorBound_of_retained
    hTraceyHalf hTraceyPerm block P hr hs i₀ N hretained

/-- At three blocks the derived image of the actual top has order at most
three.  Hence one ternary source character pays every possible top-derived
label; no splitting of the monomial quotient over its top is used. -/
theorem degreeFive_topDerived_card_le_three
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (hs : Nat.card block.Points = 3) :
    Nat.card (derivedSeries block.Top 1) ≤ 3 := by
  let points : block.Points ≃ Fin 3 := Finite.equivFinOfCardEq hs
  let f := degreeFiveTopRelabel block points
  let f' : derivedSeries block.Top 1 →*
      derivedSeries (Equiv.Perm (Fin 3)) 1 :=
    (f.comp (derivedSeries block.Top 1).subtype).codRestrict
      (derivedSeries (Equiv.Perm (Fin 3)) 1) (by
        intro x
        exact map_derivedSeries_le_derivedSeries f 1 ⟨x, x.2, rfl⟩)
  have hf' : Function.Injective f' := by
    intro x y hxy
    apply Subtype.ext
    apply degreeFiveTopRelabel_injective block points
    exact congrArg Subtype.val hxy
  calc
    Nat.card (derivedSeries block.Top 1) ≤
        Nat.card (derivedSeries (Equiv.Perm (Fin 3)) 1) :=
      Nat.card_le_card_of_injective f' hf'
    _ = 3 := finThree_firstDerived_card_eq_three

/-- The image of the first derived subgroup of `R=U/E` in the actual block
top is exactly the top's first derived subgroup.  This is the literal source
of the possible ternary label in the five-point residual cells. -/
theorem degreeFive_derivedTopImage_eq
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre] :
    (derivedSeries (preE7NonPairAction w U ⧸ E block P) 1).map
        (degreeFiveQuotientTopMap block P) =
      derivedSeries block.Top 1 := by
  exact map_derivedSeries_eq
    (degreeFiveQuotientTopMap_surjective block P) 1

/-- Consequently the genuine derived top label has cardinality at most
three in the three-block residual frame. -/
theorem degreeFive_derivedTopImage_card_le_three
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (hs : Nat.card block.Points = 3) :
    Nat.card ((derivedSeries
        (preE7NonPairAction w U ⧸ E block P) 1).map
          (degreeFiveQuotientTopMap block P)) ≤ 3 := by
  rw [degreeFive_derivedTopImage_eq block P]
  exact degreeFive_topDerived_card_le_three block hs

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
