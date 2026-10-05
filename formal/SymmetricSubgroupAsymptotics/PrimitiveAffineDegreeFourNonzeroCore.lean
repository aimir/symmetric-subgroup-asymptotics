import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFiveWholeSocle
import SymmetricSubgroupAsymptotics.WholeLinearKernelSocleSharing
import SymmetricSubgroupAsymptotics.PrimeRelativeHeadZeroAbsorption
import SymmetricSubgroupAsymptotics.OddMarkerTernaryChart

/-!
# The literal nonzero ternary core in affine degree four

This module develops the actual-frame structural route for the natural
`A4`/`S4` component.  The correlated core is kept as the literal subgroup
`D = (U/E) ∩ C3^s`; it is never replaced by the full coordinate product.
The file proves coordinate fullness, zero fixed space, the retained faithful
core section, the core-active/core-fixed socle split, and the exact injection
of every core-trivial lifted section into the actual block top.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra commutatorElement

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
/-! ## The literal degree-four ternary core

After the binary translation intersection has been divided out, the actual
quotient embeds in the wreath product of the literal local complement by the
literal action on blocks.  Parity on the three nonzero translations is an
intrinsic map on that local complement.  Compressing all of its coordinate
parities at once therefore constructs exactly the manuscript subgroup

`D = (U / E) ∩ C₃^s`.

This formulation has two useful features.  The equation is not imposed as a
new structural input, and normality of `D` follows because it is the kernel
of one homomorphism on the actual quotient.  In particular, diagonal and
other correlated ternary cores are retained rather than enlarged to the
full product. -/

variable (block : OriginalMinimalBlock
  (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- The parity of the actual local complement action on the three nonzero
translations.  It is defined before using the equation `r = 4`, so the same
map remains well typed while the literal degree is being identified. -/
def degreeFourLocalBinarySign :
    LocalQuotient block P →* Multiplicative (ZMod 2) :=
  (permutationBinarySign (Fin (localDegree block))).comp
    (complementAction block P).range.subtype

/-- The quotient `R = U / E` in the exact block frame. -/
abbrev DegreeFourComplementQuotient :=
  preE7NonPairAction w U ⧸ E block P

/-- Projection of `R` onto the literal action on its set of blocks. -/
def degreeFourQuotientTopMap :
    DegreeFourComplementQuotient block P →* block.Top :=
  PermutationalWreathProduct.rightHom.comp (quotientEmbedding block P)

/-- The block kernel inside `R`. -/
abbrev degreeFourQuotientBlockKernel :
    Subgroup (DegreeFourComplementQuotient block P) :=
  (degreeFourQuotientTopMap block P).ker

/-- The simultaneous local-sign compression of the actual quotient.  Its
kernel is literally the intersection with the product of the local even
subgroups; in degree four these are the `C₃` coordinates. -/
def degreeFourSignedWreathMap :
    DegreeFourComplementQuotient block P →*
      PermutationalWreathProduct (Multiplicative (ZMod 2))
        block.Top block.Points :=
  (PermutationalWreathProduct.mapBase
    (degreeFourLocalBinarySign block P)).comp (quotientEmbedding block P)

/-- The actual correlated ternary core `D = R ∩ C₃^s`. -/
abbrev degreeFourTernaryCore :
    Subgroup (DegreeFourComplementQuotient block P) :=
  PermutationalWreathProduct.Compression.kernel
    (quotientEmbedding block P) (degreeFourLocalBinarySign block P)

instance degreeFourTernaryCore_normal :
    (degreeFourTernaryCore block P).Normal := by
  dsimp only [degreeFourTernaryCore]
  infer_instance

/-- Membership in the ternary core forces trivial motion on blocks. -/
theorem degreeFourTernaryCore_le_blockKernel :
    degreeFourTernaryCore block P ≤ degreeFourQuotientBlockKernel block P := by
  intro d hd
  apply MonoidHom.mem_ker.mpr
  have hcompressed :
      PermutationalWreathProduct.mapBase (degreeFourLocalBinarySign block P)
          (quotientEmbedding block P d) = 1 :=
    MonoidHom.mem_ker.mp hd
  have hright := congrArg PermutationalWreathProduct.right hcompressed
  simpa only [PermutationalWreathProduct.mapBase_right,
    PermutationalWreathProduct.one_right] using hright

/-- One retained `C₃` coordinate of the literal core. -/
def degreeFourTernaryCoordinate (i : block.Points) :
    degreeFourTernaryCore block P →* (degreeFourLocalBinarySign block P).ker :=
  PermutationalWreathProduct.Compression.kernelCoordinate
    (quotientEmbedding block P) (degreeFourLocalBinarySign block P) i

/-- The literal core coordinates are jointly faithful.  Thus later module
arguments can work in the actual correlated subspace without replacing it
by `C₃^s`. -/
theorem degreeFourTernaryCoordinate_joint_injective :
    Function.Injective (fun d i ↦ degreeFourTernaryCoordinate block P i d) :=
  PermutationalWreathProduct.Compression.kernelCoordinate_joint_injective
    (quotientEmbedding block P) (degreeFourLocalBinarySign block P)
    (quotientEmbedding_injective block P)

/-- Compression by the surjective affine projection preserves the exact
local component of the actual block embedding. -/
theorem degreeFourQuotient_fullComponent :
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

/-- Each displayed coordinate image of the actual ternary core is normal in
the local even subgroup.  This is the precise coordinate-normality needed
by the induced-module argument. -/
theorem degreeFourTernaryCoordinate_range_normal (i : block.Points) :
    (degreeFourTernaryCoordinate block P i).range.Normal :=
  PermutationalWreathProduct.Compression.kernelCoordinate_range_normal
    (quotientEmbedding block P) (degreeFourLocalBinarySign block P)
    (degreeFourQuotient_fullComponent block P) i

/-- Ambient conjugation transports a ternary-core coordinate to the
corresponding transported block. -/
theorem degreeFourTernaryCoordinate_conjugation
    (a : DegreeFourComplementQuotient block P)
    (d : degreeFourTernaryCore block P) (i : block.Points) :
    ((degreeFourTernaryCoordinate block P
        ((quotientEmbedding block P a).right • i)
        (MulAut.conjNormal a d) :
      (degreeFourLocalBinarySign block P).ker) : LocalQuotient block P) =
      (quotientEmbedding block P a).left
          ((quotientEmbedding block P a).right • i) *
        (degreeFourTernaryCoordinate block P i d :
          (degreeFourLocalBinarySign block P).ker) *
        ((quotientEmbedding block P a).left
          ((quotientEmbedding block P a).right • i))⁻¹ := by
  change (quotientEmbedding block P (a * d.1 * a⁻¹)).left
      ((quotientEmbedding block P a).right • i) = _
  rw [map_mul, map_mul, map_inv]
  have hdright : (quotientEmbedding block P d.1).right = 1 :=
    ((PermutationalWreathProduct.mem_mapBase_ker_iff
      (degreeFourLocalBinarySign block P)
      (quotientEmbedding block P d.1)).mp d.2).1
  simp [PermutationalWreathProduct.mul_left,
    PermutationalWreathProduct.mul_right,
    PermutationalWreathProduct.inv_left, hdright, smul_smul]
  rfl

/-- The quotient still maps onto the literal transitive block top. -/
theorem degreeFourQuotientTopMap_surjective :
    Function.Surjective (degreeFourQuotientTopMap block P) := by
  intro q
  obtain ⟨g, hg⟩ := q.2
  refine ⟨QuotientGroup.mk' (E block P) g, ?_⟩
  change (block.topMap.rangeRestrict g : block.Top) = q
  exact Subtype.ext hg

/-- On the fixed three-point type the two binary sign characters have the
same kernel.  The explicit transport across the two propositionally equal
`DecidableEq` instances is needed because `permutationBinarySign` is defined
in a classical section whereas the odd-marker chart uses the native finite
instance. -/
private theorem permutationBinarySign_eq_one_iff_oddMarkerSign_eq_one
    (g : Equiv.Perm (Fin 3)) :
    permutationBinarySign (Fin 3) g = 1 ↔ oddMarkerSign g = 1 := by
  rw [permutationBinarySign_eq_one, oddMarkerSign_eq_one]
  constructor
  · intro hs
    rw [@Equiv.Perm.sign_eq_sign_of_equiv
      (Fin 3) (instDecidableEqFin 3) (Fin 3) inferInstance
      (fun a b => Classical.propDecidable (a = b)) inferInstance
      g g (Equiv.refl _) (fun _ => rfl)]
    exact hs
  · intro hs
    rw [← @Equiv.Perm.sign_eq_sign_of_equiv
      (Fin 3) (instDecidableEqFin 3) (Fin 3) inferInstance
      (fun a b => Classical.propDecidable (a = b)) inferInstance
      g g (Equiv.refl _) (fun _ => rfl)]
    exact hs

private theorem binarySignKernel_finThree_card_of_card_three_or_six
    {n : ℕ} (A : Subgroup (Equiv.Perm (Fin n)))
    (hn : n = 3)
    (hA : Nat.card A = 3 ∨ Nat.card A = 6) :
    Nat.card ((permutationBinarySign (Fin n)).comp A.subtype).ker = 3 := by
  subst n
  let f := (permutationBinarySign (Fin 3)).comp A.subtype
  have hmul := f.ker.card_mul_index
  rw [Subgroup.index_ker] at hmul
  have hrange : Nat.card f.range ≤ 2 := by
    calc
      Nat.card f.range ≤ Nat.card (Multiplicative (ZMod 2)) :=
        Subgroup.card_le_card_group f.range
      _ = 2 := by simp
  rcases hA with hA | hA
  · rw [hA] at hmul
    have hcases : Nat.card f.range = 1 ∨ Nat.card f.range = 2 := by
      have hpos : 0 < Nat.card f.range := Nat.card_pos
      omega
    rcases hcases with hrangeOne | hrangeTwo
    · simpa only [hrangeOne, Nat.mul_one] using hmul
    · have hk : Nat.card f.ker * 2 = 3 := by
        simpa only [hrangeTwo, hA] using hmul
      omega
  · have hAtop : A = ⊤ := by
      apply A.eq_top_of_card_eq
      exact hA.trans (by
        norm_num [Nat.card_eq_fintype_card, Fintype.card_perm])
    let t : A :=
      ⟨Equiv.swap (0 : Fin 3) 1, by rw [hAtop]; exact Subgroup.mem_top _⟩
    have ht : f t ≠ 1 := by
      change permutationBinarySign (Fin 3) (Equiv.swap 0 1) ≠ 1
      intro hsign
      have hodd : oddMarkerSign (Equiv.swap (0 : Fin 3) 1) = 1 :=
        (permutationBinarySign_eq_one_iff_oddMarkerSign_eq_one _).1 hsign
      have hs := (oddMarkerSign_eq_one _).1 hodd
      rw [Equiv.Perm.sign_swap (by decide : (0 : Fin 3) ≠ 1)] at hs
      norm_num at hs
    have hrange_ne_one : Nat.card f.range ≠ 1 := by
      intro hone
      have hrange_subsingleton : Subsingleton f.range :=
        Finite.card_le_one_iff_subsingleton.mp hone.le
      have heq : (⟨f t, ⟨t, rfl⟩⟩ : f.range) = 1 :=
        @Subsingleton.elim f.range hrange_subsingleton _ _
      exact ht (congrArg Subtype.val heq)
    have hcases : Nat.card f.range = 1 ∨ Nat.card f.range = 2 := by
      have hpos : 0 < Nat.card f.range := Nat.card_pos
      omega
    have hrangeTwo : Nat.card f.range = 2 := hcases.resolve_left hrange_ne_one
    have hk : Nat.card f.ker * 2 = 6 := by
      simpa only [hrangeTwo, hA] using hmul
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < (2 : ℕ))
      (by simpa only [show 6 = 3 * 2 by norm_num] using hk)

/-- The local even subgroup has order three in both literal possibilities
`A₄ / V₄ = C₃` and `S₄ / V₄ = S₃`.  The only finite
recognition used here is the preceding kernel-checked statement for
subgroups of `S₃`. -/
theorem degreeFourLocalBinarySign_ker_card
    (hr : Nat.card block.Fibre = 4) :
    Nat.card (degreeFourLocalBinarySign block P).ker = 3 := by
  have hlocalDegree : localDegree block = 3 := by
    simp only [localDegree, hr]
  have hcomplement := degreeFour_complement_card_eq_three_or_six block P hr
  have hlocal : Nat.card (LocalQuotient block P) = 3 ∨
      Nat.card (LocalQuotient block P) = 6 := by
    have hcard : Nat.card (LocalQuotient block P) =
        Nat.card (P.complement (origin block)) :=
      Nat.card_congr (degreeFiveLocalComplementEquiv block P).symm.toEquiv
    simpa only [hcard] using hcomplement
  exact binarySignKernel_finThree_card_of_card_three_or_six
    (complementAction block P).range hlocalDegree hlocal

/-- The local `C₃` has no fixed vector on the literal binary translation
plane.  This is derived from normality, irreducibility, and faithfulness of
the exact local affine action, rather than from an abstract `A₄`/`S₄`
label. -/
theorem degreeFourLocalTernary_invariants_eq_bot
    (hr : Nat.card block.Fibre = 4) :
    let C := chart block P
    letI : Fact P.p.Prime := C.primeFact
    Representation.invariants
      ((degreeFiveLocalLinearRepresentation block P).ρ.comp
        (degreeFourLocalBinarySign block P).ker.subtype) = ⊥ := by
  let C := chart block P
  letI : Fact P.p.Prime := C.primeFact
  let D := (degreeFourLocalBinarySign block P).ker
  let ρ := (degreeFiveLocalLinearRepresentation block P).ρ
  let W : Subrepresentation ρ :=
    { toSubmodule := Representation.invariants (ρ.comp D.subtype)
      apply_mem_toSubmodule := by
        intro g v hv
        exact Representation.le_comap_invariants ρ D g hv }
  letI : Representation.IsIrreducible ρ :=
    degreeFiveLocalLinearRepresentation_irreducible block P
  rcases (inferInstance : Representation.IsIrreducible ρ)
      |>.eq_bot_or_eq_top W with hbot | htop
  · exact congrArg Subrepresentation.toSubmodule hbot
  · exfalso
    have hD : D ≠ ⊥ := by
      intro h
      have hcard : Nat.card D = 1 := by rw [h, Subgroup.card_bot]
      rw [degreeFourLocalBinarySign_ker_card block P hr] at hcard
      omega
    apply hD
    rw [eq_bot_iff]
    intro d hd
    apply Subgroup.mem_bot.mpr
    have hρd : ρ d = 1 := by
      ext v
      have hvW : v ∈ W := by rw [htop]; exact Submodule.mem_top
      exact hvW ⟨d, hd⟩
    exact (degreeFiveLocalLinearRepresentation_injective block P)
      (hρd.trans (map_one ρ).symm)

/-- Equivalently, every nonzero local translation vector is moved by some
element of the literal local ternary subgroup. -/
theorem degreeFourLocalTernary_exists_moves
    (hr : Nat.card block.Fibre = 4)
    (v : (chart block P).V) (hv : v ≠ 0) :
    ∃ d : (degreeFourLocalBinarySign block P).ker,
      (degreeFiveLocalLinearRepresentation block P).ρ d.1 v ≠ v := by
  by_contra hall
  push_neg at hall
  have hvInv : v ∈ Representation.invariants
      ((degreeFiveLocalLinearRepresentation block P).ρ.comp
        (degreeFourLocalBinarySign block P).ker.subtype) := by
    intro d
    exact hall d
  rw [degreeFourLocalTernary_invariants_eq_bot block P hr] at hvInv
  exact hv (by simpa only [Submodule.mem_bot] using hvInv)

/-- A nonzero normal ternary core projects onto the local `C₃` at every
block.  Normality, the transitive literal top, and the prime local order are
all used here; no product decomposition of the core is used. -/
theorem degreeFourTernaryCoordinate_surjective
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P ≠ ⊥)
    (i : block.Points) :
    Function.Surjective (degreeFourTernaryCoordinate block P i) := by
  obtain ⟨d, hdne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hD
  have hsome : ∃ i₀ : block.Points,
      degreeFourTernaryCoordinate block P i₀ d ≠ 1 := by
    by_contra hnone
    push_neg at hnone
    apply hdne
    apply degreeFourTernaryCoordinate_joint_injective block P
    funext i₀
    simpa only [map_one] using hnone i₀
  obtain ⟨i₀, hi₀⟩ := hsome
  letI : MulAction.IsPretransitive block.Top block.Points :=
    block.top_pretransitive
  obtain ⟨q, hq⟩ := MulAction.exists_smul_eq block.Top i₀ i
  obtain ⟨a, ha⟩ := degreeFourQuotientTopMap_surjective block P q
  let d' : degreeFourTernaryCore block P := MulAut.conjNormal a d
  have hd' : degreeFourTernaryCoordinate block P i d' ≠ 1 := by
    intro hdone
    have hformula := degreeFourTernaryCoordinate_conjugation block P a d i₀
    have hright : (quotientEmbedding block P a).right = q := ha
    rw [hright, hq] at hformula
    have hconj :
        (quotientEmbedding block P a).left i *
            (degreeFourTernaryCoordinate block P i₀ d :
              (degreeFourLocalBinarySign block P).ker) *
            ((quotientEmbedding block P a).left i)⁻¹ = 1 := by
      rw [← hformula]
      exact congrArg Subtype.val hdone
    exact hi₀ (Subtype.ext ((conj_eq_one_iff).mp hconj))
  have hrange_ne : (degreeFourTernaryCoordinate block P i).range ≠ ⊥ := by
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    refine ⟨⟨degreeFourTernaryCoordinate block P i d', ⟨d', rfl⟩⟩, ?_⟩
    intro h
    exact hd' (congrArg Subtype.val h)
  letI : Fact (Nat.card (degreeFourLocalBinarySign block P).ker).Prime :=
    ⟨(degreeFourLocalBinarySign_ker_card block P hr).symm ▸ by norm_num⟩
  have hrange_top : (degreeFourTernaryCoordinate block P i).range = ⊤ :=
    (degreeFourTernaryCoordinate block P i).range
      |>.eq_bot_or_eq_top_of_prime_card |>.resolve_left hrange_ne
  exact MonoidHom.range_eq_top.mp hrange_top

/-- The actual nonzero correlated ternary core has zero fixed space on the
entire correlated binary translation module.  A nonzero global vector has
a nonzero literal coordinate; surjectivity of the corresponding core
coordinate supplies a local `C₃` element which moves it. -/
theorem degreeFourTernaryCore_global_invariants_eq_bot
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P ≠ ⊥) :
    let C := elementaryChart block P
    Representation.invariants
      (C.quotientRepresentation.ρ.comp
        (degreeFourTernaryCore block P).subtype) = ⊥ := by
  let C := elementaryChart block P
  apply le_bot_iff.mp
  intro v hvInv
  rw [Submodule.mem_bot]
  by_contra hv
  have hsome : ∃ i : block.Points, v.1 i ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hv
    apply Subtype.ext
    funext i
    exact hall i
  obtain ⟨i, hi⟩ := hsome
  obtain ⟨d, hdmove⟩ :=
    degreeFourLocalTernary_exists_moves block P hr (v.1 i) hi
  obtain ⟨z, hz⟩ := degreeFourTernaryCoordinate_surjective
    block P hr hD i d
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (E block P) z.1
  have hzTop : z.1 ∈ degreeFourQuotientBlockKernel block P :=
    degreeFourTernaryCore_le_blockKernel block P z.2
  have hgRight : (ambientEmbedding block g).right = 1 := by
    have htop : (quotientEmbedding block P z.1).right = 1 :=
      MonoidHom.mem_ker.mp hzTop
    rw [← hg] at htop
    exact htop
  have hgTop : block.topMap g = 1 := by
    simpa only [ambientEmbedding, ActualBlockWreathEmbedding.embedding]
      using congrArg Subtype.val hgRight
  obtain ⟨e, he⟩ := C.equiv.surjective (Multiplicative.ofAdd v)
  have heAdd : (C.equiv e).toAdd = v :=
    congrArg Multiplicative.toAdd he
  have hchartFix :
      (C.equiv (MulAut.conjNormal g e)).toAdd = (C.equiv e).toAdd := by
    rw [← C.quotientRepresentation_apply g e, hg, heAdd]
    exact hvInv z
  have hcoordinateFix :
      (coordinate block P i (MulAut.conjNormal g e)).toAdd =
        (coordinate block P i e).toAdd := by
    rw [← degreeFive_elementaryChart_equiv_coordinate]
    rw [← degreeFive_elementaryChart_equiv_coordinate]
    exact congrArg (fun x : C.V ↦ x.1 i) hchartFix
  have hlocal :
      localMap block P ((ambientEmbedding block g).left i) = d.1 := by
    have hzval := congrArg Subtype.val hz
    change (quotientEmbedding block P
      (QuotientGroup.mk' (E block P) g)).left i = d.1
    rw [hg]
    exact hzval
  have hcoordinateAction := degreeFive_coordinate_conjugation_of_top_fixed
    block P hTraceyPerm g e i (by rw [hgTop]; exact one_smul _ _)
  rw [hlocal, hcoordinateFix] at hcoordinateAction
  have hecoord : (coordinate block P i e).toAdd = v.1 i := by
    have heval := congrArg (fun x : C.V ↦ x.1 i) heAdd
    simpa only [C, degreeFive_elementaryChart_equiv_coordinate] using heval
  rw [hecoord] at hcoordinateAction
  exact hdmove hcoordinateAction.symm

/-- The literal action of the retained ternary core on the correlated
binary translation space.  Naming the action keeps later Maschke formulas
independent of coercion parsing for bundled representations. -/
def degreeFourTernaryAction
    (d : degreeFourTernaryCore block P)
    (v : (elementaryChart block P).V) :
    (elementaryChart block P).V :=
  (elementaryChart block P).quotientRepresentation.ρ d.1 v

/-- Maschke's theorem makes the zero-fixed-space conclusion survive every
literal quotient of the correlated translation module.  This formulation
keeps the quotient as its actual invariant intersection `I`: a vector
which is fixed modulo `I` has a representative in an invariant complement,
and that representative would be fixed already in the original module. -/
theorem degreeFour_no_fixed_vector_mod_normalSubrepresentation
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P ≠ ⊥)
    (N : Subgroup (preE7NonPairAction w U)) [N.Normal]
    (v : (elementaryChart block P).V)
    (hv : v ∉
      (elementaryChart block P).originalKernelChart.normalSubrepresentation
        (QuotientGroup.mk' (E block P))
        (QuotientGroup.mk'_surjective (E block P))
        (elementaryChart block P).quotientRepresentation N)
    (hfixedMod : ∀ d : degreeFourTernaryCore block P,
      degreeFourTernaryAction block P d v - v ∈
        (elementaryChart block P).originalKernelChart.normalSubrepresentation
          (QuotientGroup.mk' (E block P))
          (QuotientGroup.mk'_surjective (E block P))
          (elementaryChart block P).quotientRepresentation N) :
    False := by
  let C := elementaryChart block P
  let D := degreeFourTernaryCore block P
  let ρD := C.quotientRepresentation.ρ.comp D.subtype
  let act : D → C.V → C.V := fun d x ↦ ρD d x
  let I₀ := C.originalKernelChart.normalSubrepresentation
    (QuotientGroup.mk' (E block P))
    (QuotientGroup.mk'_surjective (E block P))
    C.quotientRepresentation N
  let I : Subrepresentation ρD :=
    { toSubmodule := I₀.toSubmodule
      apply_mem_toSubmodule := by
        intro d x hx
        exact I₀.apply_mem_toSubmodule d.1 hx }
  let κ : D →* (block.Points →
      (degreeFourLocalBinarySign block P).ker) :=
    { toFun := fun d i ↦ degreeFourTernaryCoordinate block P i d
      map_one' := funext fun i ↦ map_one _
      map_mul' := fun x y ↦ funext fun i ↦ map_mul _ _ _ }
  have hκ : Function.Injective κ :=
    degreeFourTernaryCoordinate_joint_injective block P
  have hcardDvd : Nat.card D ∣ 3 ^ Nat.card block.Points := by
    have hdiv := Subgroup.card_dvd_of_injective κ hκ
    simpa only [Nat.card_fun,
      degreeFourLocalBinarySign_ker_card block P hr] using hdiv
  have hp : C.p = 2 := by
    change P.p = 2
    let C₀ := chart block P
    letI : Finite C₀.V := Finite.of_injective
      (fun x : C₀.V ↦ C₀.equiv.symm (Multiplicative.ofAdd x))
      C₀.equiv.symm.injective
    have hdegree : 4 = P.p ^ C₀.d := by
      rw [← hr]
      simpa [PrimitiveAffineProfile.ElementaryChart.d] using
        P.degree_eq_prime_pow_finrank C₀.equiv (origin block)
    exact (prime_pow_positive_injective (d := C₀.d) (e := 2)
      P.p_prime Nat.prime_two C₀.d_pos (by norm_num)
        (hdegree.symm.trans (by norm_num))).1
  letI : NeZero (Nat.card D : ZMod C.p) := by
    constructor
    intro hzero
    have hdiv : C.p ∣ Nat.card D :=
      (ZMod.natCast_eq_zero_iff _ _).mp hzero
    have hp3pow : C.p ∣ 3 ^ Nat.card block.Points := hdiv.trans hcardDvd
    have hp3 : C.p ∣ 3 := C.p_prime.dvd_of_dvd_pow hp3pow
    have heq : C.p = 3 :=
      (Nat.prime_dvd_prime_iff_eq C.p_prime Nat.prime_three).mp hp3
    omega
  obtain ⟨J, hIJ⟩ := exists_isCompl I
  have hvSup : v ∈ I.toSubmodule ⊔ J.toSubmodule := by
    have hvTop : v ∈ (⊤ : Subrepresentation ρD) := Submodule.mem_top
    rw [← hIJ.codisjoint.eq_top] at hvTop
    exact hvTop
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp hvSup
  have hjne : j ≠ 0 := by
    intro hjzero
    subst j
    simp only [add_zero] at hij
    apply hv
    change v ∈ I₀
    rw [← hij]
    exact hi
  have hjfixed : j ∈ Representation.invariants ρD := by
    intro d
    have htotal : act d v - v ∈ I := by
      simpa only [act, ρD, degreeFourTernaryAction, C, D] using hfixedMod d
    have hiDiff : act d i - i ∈ I :=
      I.toSubmodule.sub_mem (I.apply_mem_toSubmodule d hi) hi
    have hjDiffI : act d j - j ∈ I := by
      have heq : act d j - j =
          (act d v - v) - (act d i - i) := by
        dsimp only [act]
        rw [← hij, map_add]
        simp only [sub_eq_add_neg, neg_smul, one_smul]
        abel
      rw [heq]
      exact I.toSubmodule.sub_mem htotal hiDiff
    have hjDiffJ : act d j - j ∈ J :=
      J.toSubmodule.sub_mem (J.apply_mem_toSubmodule d hj) hj
    have hInf : act d j - j ∈ (I ⊓ J : Subrepresentation ρD) :=
      ⟨hjDiffI, hjDiffJ⟩
    have hbot : act d j - j ∈ (⊥ : Submodule (ZMod C.p) C.V) := by
      rw [hIJ.disjoint.eq_bot] at hInf
      exact hInf
    exact sub_eq_zero.mp (by simpa only [Submodule.mem_bot] using hbot)
  have hjzero : j = 0 := by
    have hjbot : j ∈ (⊥ : Submodule (ZMod C.p) C.V) := by
      rw [← degreeFourTernaryCore_global_invariants_eq_bot
        block P hTraceyPerm hr hD]
      exact hjfixed
    simpa only [Submodule.mem_bot] using hjbot
  exact hjne hjzero

/-- The ternary core is abelian.  This is proved through its actual jointly
faithful coordinates, and hence also covers diagonal cores. -/
theorem degreeFourTernaryCore_commute
    (hr : Nat.card block.Fibre = 4)
    (x y : degreeFourTernaryCore block P) : Commute x y := by
  letI : Fact (Nat.card (degreeFourLocalBinarySign block P).ker).Prime :=
    ⟨(degreeFourLocalBinarySign_ker_card block P hr).symm ▸ by norm_num⟩
  letI : IsCyclic (degreeFourLocalBinarySign block P).ker :=
    isCyclic_of_prime_card rfl
  letI : CommGroup (degreeFourLocalBinarySign block P).ker :=
    IsCyclic.commGroup
  apply degreeFourTernaryCoordinate_joint_injective block P
  funext i
  simpa only [map_mul] using
    (mul_comm (degreeFourTernaryCoordinate block P i x)
      (degreeFourTernaryCoordinate block P i y))

private theorem centralizes_fullBinarySignKernel_mem_kernel_finThree :
    ∀ a : Equiv.Perm (Fin 3),
      (∀ d : (permutationBinarySign (Fin 3)).ker, a * d.1 = d.1 * a) →
        a ∈ (permutationBinarySign (Fin 3)).ker := by
  intro a ha
  let z : Multiplicative (ZMod 3) := Multiplicative.ofAdd 1
  let d : (permutationBinarySign (Fin 3)).ker :=
    ⟨OddMarkerTernaryChart.chart z, by
      apply MonoidHom.mem_ker.mpr
      exact (permutationBinarySign_eq_one_iff_oddMarkerSign_eq_one _).2
        (OddMarkerTernaryChart.chart z).2⟩
  have hconj : a * d.1 * a⁻¹ = d.1 := by
    rw [ha d]
    simp
  have hz : Multiplicative.ofAdd
      (OddMarkerTernaryChart.signScalar (oddMarkerSign a) * z.toAdd) = z := by
    apply OddMarkerTernaryChart.chart.injective
    apply Subtype.ext
    exact (OddMarkerTernaryChart.chart_conjugate_coe a z).symm.trans hconj
  have hscalar : OddMarkerTernaryChart.signScalar (oddMarkerSign a) = 1 := by
    have hzadd := congrArg Multiplicative.toAdd hz
    simpa only [z, toAdd_ofAdd, mul_one] using hzadd
  have hodd : oddMarkerSign a = 1 :=
    OddMarkerTernaryChart.signScalar_injective
      (hscalar.trans OddMarkerTernaryChart.signScalar_one.symm)
  apply MonoidHom.mem_ker.mpr
  exact (permutationBinarySign_eq_one_iff_oddMarkerSign_eq_one a).2 hodd

private theorem centralizes_binarySignKernel_mem_kernel_finThree
    {n : ℕ} (A : Subgroup (Equiv.Perm (Fin n)))
    (hn : n = 3)
    (hA : Nat.card A = 3 ∨ Nat.card A = 6)
    (a : A)
    (ha : ∀ d : ((permutationBinarySign (Fin n)).comp A.subtype).ker,
      Commute a d.1) :
    a ∈ ((permutationBinarySign (Fin n)).comp A.subtype).ker := by
  subst n
  let f := (permutationBinarySign (Fin 3)).comp A.subtype
  have hker : Nat.card f.ker = 3 :=
    binarySignKernel_finThree_card_of_card_three_or_six A rfl hA
  rcases hA with hA | hA
  · have htop : f.ker = ⊤ := by
      apply f.ker.eq_top_of_card_eq
      exact hker.trans hA.symm
    rw [htop]
    exact Subgroup.mem_top a
  · have hAtop : A = ⊤ := by
      apply A.eq_top_of_card_eq
      exact hA.trans (by
        norm_num [Nat.card_eq_fintype_card, Fintype.card_perm])
    have hall : ∀ d : (permutationBinarySign (Fin 3)).ker,
        (a.1 : Equiv.Perm (Fin 3)) * d.1 = d.1 * a.1 := by
      intro d
      let dA : A := ⟨d.1, by rw [hAtop]; exact Subgroup.mem_top _⟩
      have hdA : dA ∈ f.ker := by
        exact d.2
      change a.1 * d.1 = d.1 * a.1
      exact congrArg Subtype.val (ha ⟨dA, hdA⟩).eq
    exact centralizes_fullBinarySignKernel_mem_kernel_finThree a.1 hall

/-- In the literal local `C₃` or `S₃`, an element centralizing the even
subgroup already belongs to that even subgroup. -/
theorem degreeFourLocal_mem_signKernel_of_centralizes
    (hr : Nat.card block.Fibre = 4)
    (a : LocalQuotient block P)
    (ha : ∀ d : (degreeFourLocalBinarySign block P).ker,
      Commute a d.1) :
    a ∈ (degreeFourLocalBinarySign block P).ker := by
  have hlocalDegree : localDegree block = 3 := by
    simp only [localDegree, hr]
  have hcomplement := degreeFour_complement_card_eq_three_or_six block P hr
  have hlocal : Nat.card (LocalQuotient block P) = 3 ∨
      Nat.card (LocalQuotient block P) = 6 := by
    have hcard : Nat.card (LocalQuotient block P) =
        Nat.card (P.complement (origin block)) :=
      Nat.card_congr (degreeFiveLocalComplementEquiv block P).symm.toEquiv
    simpa only [hcard] using hcomplement
  exact centralizes_binarySignKernel_mem_kernel_finThree
    (complementAction block P).range hlocalDegree hlocal a ha

/-- Inside the block kernel, the centralizer of a nonzero ternary core is
exactly that core.  This is the formal faithful-core-section statement used
to send every disjoint socle type into the top action. -/
theorem degreeFourTernaryCore_centralizer_inf_blockKernel
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P ≠ ⊥) :
    Subgroup.centralizer
        (degreeFourTernaryCore block P :
          Set (DegreeFourComplementQuotient block P)) ⊓
      degreeFourQuotientBlockKernel block P =
        degreeFourTernaryCore block P := by
  apply le_antisymm
  · rintro a ⟨haCentral, haTop⟩
    change quotientEmbedding block P a ∈
      (PermutationalWreathProduct.mapBase
        (degreeFourLocalBinarySign block P)).ker
    apply (PermutationalWreathProduct.mem_mapBase_ker_iff
      (degreeFourLocalBinarySign block P)
      (quotientEmbedding block P a)).mpr
    have hatop : (quotientEmbedding block P a).right = 1 :=
      MonoidHom.mem_ker.mp haTop
    refine ⟨hatop, ?_⟩
    intro i
    apply degreeFourLocal_mem_signKernel_of_centralizes block P hr
    intro z
    obtain ⟨d, hd⟩ := degreeFourTernaryCoordinate_surjective
      block P hr hD i z
    have hdtop : (quotientEmbedding block P d.1).right = 1 :=
      ((PermutationalWreathProduct.mem_mapBase_ker_iff
        (degreeFourLocalBinarySign block P)
        (quotientEmbedding block P d.1)).mp d.2).1
    have hcomm : d.1 * a = a * d.1 :=
      Subgroup.mem_centralizer_iff.mp haCentral d.1 d.2
    have hleft := congrArg
      (fun x : DegreeFourComplementQuotient block P ↦
        (quotientEmbedding block P x).left i) hcomm
    change (quotientEmbedding block P (d.1 * a)).left i =
      (quotientEmbedding block P (a * d.1)).left i at hleft
    rw [map_mul, map_mul,
      PermutationalWreathProduct.mul_left,
      PermutationalWreathProduct.mul_left, hatop, hdtop] at hleft
    simp only [inv_one, one_smul] at hleft
    change ((quotientEmbedding block P a).left i) * z.1 =
      z.1 * ((quotientEmbedding block P a).left i)
    rw [← hd]
    exact hleft.symm
  · intro d hd
    refine ⟨?_, degreeFourTernaryCore_le_blockKernel block P hd⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro e he
    exact congrArg Subtype.val
      (degreeFourTernaryCore_commute block P hr
        ⟨e, he⟩ ⟨d, hd⟩).eq

/-- Restrict the literal top projection to a chosen normal or socle
subgroup of `R`. -/
def degreeFourRestrictedTopMap
    (H : Subgroup (DegreeFourComplementQuotient block P)) :
    H →* block.Top :=
  (degreeFourQuotientTopMap block P).comp H.subtype

/-- Every subgroup which centralizes `D` and is disjoint from `D` embeds in
the actual top.  This is the reusable top-injection half of the manuscript's
disjoint-type/max argument. -/
theorem degreeFourRestrictedTopMap_injective_of_centralizes_disjoint
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P ≠ ⊥)
    (H : Subgroup (DegreeFourComplementQuotient block P))
    (hcentral : H ≤ Subgroup.centralizer
      (degreeFourTernaryCore block P :
        Set (DegreeFourComplementQuotient block P)))
    (hdisjoint : H ⊓ degreeFourTernaryCore block P = ⊥) :
    Function.Injective (degreeFourRestrictedTopMap block P H) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_antisymm
  · intro x hx
    have hxTop : (x.1 : DegreeFourComplementQuotient block P) ∈
        degreeFourQuotientBlockKernel block P :=
      MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hx)
    have hxCentral := hcentral x.2
    have hxD : (x.1 : DegreeFourComplementQuotient block P) ∈
        degreeFourTernaryCore block P := by
      rw [← degreeFourTernaryCore_centralizer_inf_blockKernel
        block P hr hD]
      exact ⟨hxCentral, hxTop⟩
    have hxInf : (x.1 : DegreeFourComplementQuotient block P) ∈
        H ⊓ degreeFourTernaryCore block P := ⟨x.2, hxD⟩
    rw [hdisjoint] at hxInf
    exact Subtype.ext (Subgroup.mem_bot.mp hxInf)
  · exact bot_le

/-- Any selected normal subgroup which embeds in the actual block top has
at most the literal block degree in ambient normal generators.  This is the
direct entry point for the published permutation-section theorem; it avoids
enumerating the prime types occurring in the outer socle. -/
theorem degreeFourTopEmbedded_normalGen_le
    (hgen : PermutationSubgroupGeneratorBound)
    (hs : 2 ≤ Nat.card block.Points)
    {G : Type} [Group G] [Finite G]
    (H : Subgroup G) [H.Normal]
    (f : H →* block.Top) (hf : Function.Injective f) :
    MarkedC4.normalGen H ≤ Nat.card block.Points := by
  let points : block.Points ≃ Fin (Nat.card block.Points) :=
    Finite.equivFin block.Points
  let τ : block.Top →* Equiv.Perm (Fin (Nat.card block.Points)) :=
    points.permCongrHom.toMonoidHom.comp block.Top.subtype
  have hτ : Function.Injective τ :=
    points.permCongrHom.injective.comp Subtype.val_injective
  let R : Subgroup (Equiv.Perm (Fin (Nat.card block.Points))) := τ.range
  let eR : block.Top ≃* R := MulEquiv.ofBijective τ.rangeRestrict
    ⟨MonoidHom.rangeRestrict_injective_iff.mpr hτ,
      τ.rangeRestrict_surjective⟩
  exact normalGen_normalSubgroup_le_degree_of_permutationSection hgen
    R eR.symm.toMonoidHom eR.symm.surjective H
    f hf hs

/-- The actual correlated core has order at most that of the ambient
`C₃^s`; no direct-product equality is asserted. -/
theorem degreeFourTernaryCore_card_le
    (hr : Nat.card block.Fibre = 4) :
    Nat.card (degreeFourTernaryCore block P) ≤
      3 ^ Nat.card block.Points := by
  calc
    Nat.card (degreeFourTernaryCore block P) ≤
        Nat.card (block.Points → (degreeFourLocalBinarySign block P).ker) :=
      Nat.card_le_card_of_injective
        (fun d i ↦ degreeFourTernaryCoordinate block P i d)
        (degreeFourTernaryCoordinate_joint_injective block P)
    _ = Nat.card (degreeFourLocalBinarySign block P).ker ^
        Nat.card block.Points := Nat.card_fun
    _ = 3 ^ Nat.card block.Points := by
      rw [degreeFourLocalBinarySign_ker_card block P hr]

/-- Canonical prime-field coordinates on the local `C₃`. -/
noncomputable def degreeFourLocalTernaryEquiv
    (hr : Nat.card block.Fibre = 4) :
    Multiplicative (ZMod 3) ≃* (degreeFourLocalBinarySign block P).ker :=
  mulEquivOfPrimeCardEq (by simp) (degreeFourLocalBinarySign_ker_card block P hr)

/-- The exact elementary chart on the correlated core `D`.  Its vector
space is the literal image in `(F₃)^s`, so diagonal cores keep their true
dimension. -/
noncomputable def degreeFourTernaryCoreChart
    (hr : Nat.card block.Fibre = 4) :
    ElementaryMinimalNormalChart (degreeFourTernaryCore block P) :=
  PermutationalWreathProduct.Compression.kernelElementaryChart
    (p := 3) (quotientEmbedding block P)
    (degreeFourLocalBinarySign block P)
    (degreeFourLocalTernaryEquiv block P hr)
    (quotientEmbedding_injective block P)

/-- The actual wreath-compression state after removing the binary
translation intersection.  Its ambient group is `R`, its local group is the
literal `C₃` or `S₃` complement, and its displayed embedding is the one
used in the definitions above. -/
noncomputable abbrev degreeFourComplementState
    (hTraceyPerm : TraceyPermutationGeneratorInput) :=
  (initialState hTraceyPerm block).quotient
    (LocalQuotient block P) (localMap block P)
    (localMap_surjective block P)

/-- Prime-field chart of the local even subgroup. -/
noncomputable def degreeFourLocalTernaryChart
    (hr : Nat.card block.Fibre = 4) :
    ElementaryMinimalNormalChart (degreeFourLocalBinarySign block P).ker :=
  { p := 3
    p_prime := by norm_num
    primeFact := ⟨by norm_num⟩
    V := ZMod 3
    addCommGroup := inferInstance
    module := inferInstance
    finiteDimensional := inferInstance
    equiv := (degreeFourLocalTernaryEquiv block P hr).symm }

/-- Tracey's published half-dimension theorem applied to the actual frame
normally generates the correlated ternary-core module with at most
`floor(s/2)` vectors.  This is the sharp `D ≠ 1` input used in the
whole-socle proof; it is a theorem about the literal core, not the full
coordinate product.  Nontriviality is deliberately not needed here. -/
theorem degreeFourTernaryCore_representationGeneratedBy_half
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 4)
    (i₀ : block.Points) :
    RepresentationGeneratedBy
      (ActualWreathAffineCapacity.ambientRepresentation
        (degreeFourComplementState block P hTraceyPerm)
        (degreeFourLocalBinarySign block P)
        (degreeFourLocalTernaryChart block P hr))
      (Nat.card block.Points / 2) := by
  let S := degreeFourComplementState block P hTraceyPerm
  let C := degreeFourLocalTernaryChart block P hr
  have hindex : 2 ≤ (S.topPointStabilizer i₀).index := by
    rw [S.topPointStabilizer_index i₀]
    simpa only [Fintype.card_eq_nat_card] using block.degrees_ge_two.2
  have hlocal := hTraceyHalf 3 S.A (S.topPointStabilizer i₀) hindex
    (ZMod 3) (ActualWreathAffineCapacity.localRepresentation S
      (degreeFourLocalBinarySign block P) C i₀)
  have hambient := representationGeneratedBy_of_injective_of_uniform hlocal
    (ActualWreathAffineCapacity.inducedIntertwiner S
      (degreeFourLocalBinarySign block P) C i₀)
    (ActualWreathAffineCapacity.inducedIntertwiner_injective S
      (degreeFourLocalBinarySign block P) C i₀)
  rw [S.topPointStabilizer_index i₀] at hambient
  simpa only [C, degreeFourLocalTernaryChart, Module.finrank_self, one_mul,
    Fintype.card_eq_nat_card] using hambient

/-- The exact vector dimension of `D` is at most the number of blocks. -/
theorem degreeFourTernaryCoreChart_finrank_le
    (hr : Nat.card block.Fibre = 4) :
    let C := degreeFourTernaryCoreChart block P hr
    letI : AddCommGroup C.V := C.addCommGroup
    letI : Module (ZMod C.p) C.V := C.module
    letI : Fact C.p.Prime := C.primeFact
    letI : FiniteDimensional (ZMod C.p) C.V := C.finiteDimensional
    Module.finrank (ZMod C.p) C.V ≤ Nat.card block.Points := by
  let C := degreeFourTernaryCoreChart block P hr
  letI : AddCommGroup C.V := C.addCommGroup
  letI : Module (ZMod C.p) C.V := C.module
  letI : Fact C.p.Prime := C.primeFact
  letI : FiniteDimensional (ZMod C.p) C.V := C.finiteDimensional
  let S := PermutationalWreathProduct.Compression.ElementarySubmodule
    (p := 3) (quotientEmbedding block P)
    (degreeFourLocalBinarySign block P)
    (degreeFourLocalTernaryEquiv block P hr)
  change Module.finrank (ZMod 3) S ≤ Nat.card block.Points
  calc
    Module.finrank (ZMod 3) S ≤
        Module.finrank (ZMod 3) (block.Points → ZMod 3) :=
      Submodule.finrank_le S
    _ = Nat.card block.Points := by
      rw [Module.finrank_pi]
      simp

/-! ## Literal retained quotients and their two socle parts

We now keep all three quotients in the manuscript argument on their actual
groups.  For a retained normal axis `N`, `barE` is the image of the original
translation intersection in `Q = U/N`.  The subgroup `B` is the preimage in
`U` of the actual ternary core `D ≤ U/E`, and `barB` is its image in `Q`.
No abstract copy of `A4`, `S4`, or a full coordinate product occurs in these
definitions.
-/

/-- A literal normal axis of the original action. -/
abbrev DegreeFourLiteralNormalAxis :=
  {N : Subgroup (preE7NonPairAction w U) // N.Normal}

/-- The retained quotient `Q = U/N`. -/
abbrev DegreeFourRetainedQuotient
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :=
  preE7NonPairAction w U ⧸ N.1

/-- The image `barE` of the actual translation intersection in `Q`. -/
abbrev degreeFourTranslationImage
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    Subgroup (DegreeFourRetainedQuotient N) :=
  (E block P).map (QuotientGroup.mk' N.1)

instance degreeFourTranslationImage_normal
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    (degreeFourTranslationImage block P N).Normal := by
  dsimp only [degreeFourTranslationImage]
  infer_instance

/-- The full inverse image `B` of `D` in the original group. -/
abbrev degreeFourTernaryPreimage :
    Subgroup (preE7NonPairAction w U) :=
  (degreeFourTernaryCore block P).comap (QuotientGroup.mk' (E block P))

instance degreeFourTernaryPreimage_normal :
    (degreeFourTernaryPreimage block P).Normal := by
  dsimp only [degreeFourTernaryPreimage]
  infer_instance

/-- The translation intersection lies in the ternary-core preimage. -/
theorem degreeFour_translation_le_ternaryPreimage :
    E block P ≤ degreeFourTernaryPreimage block P := by
  intro e he
  change QuotientGroup.mk' (E block P) e ∈ degreeFourTernaryCore block P
  have heq : QuotientGroup.mk' (E block P) e = 1 :=
    (QuotientGroup.eq_one_iff e).2 he
  exact heq ▸ (degreeFourTernaryCore block P).one_mem

/-- Mapping `B` back to `R = U/E` recovers the literal correlated core
exactly. -/
theorem degreeFour_ternaryPreimage_map_eq_core :
    (degreeFourTernaryPreimage block P).map
        (QuotientGroup.mk' (E block P)) =
      degreeFourTernaryCore block P := by
  exact Subgroup.map_comap_eq_self_of_surjective
    (QuotientGroup.mk'_surjective (E block P)) _

/-- The image `barB` of the actual ternary-core preimage in `Q`. -/
abbrev degreeFourTernaryPreimageImage
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    Subgroup (DegreeFourRetainedQuotient N) :=
  (degreeFourTernaryPreimage block P).map (QuotientGroup.mk' N.1)

instance degreeFourTernaryPreimageImage_normal
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    (degreeFourTernaryPreimageImage block P N).Normal := by
  dsimp only [degreeFourTernaryPreimageImage]
  infer_instance

/-- The retained translation image lies in `barB`. -/
theorem degreeFour_translationImage_le_ternaryPreimageImage
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    degreeFourTranslationImage block P N ≤
      degreeFourTernaryPreimageImage block P N :=
  Subgroup.map_mono (degreeFour_translation_le_ternaryPreimage block P)

/-- An axis is retained precisely strongly enough to make `barE`
nontrivial. -/
theorem degreeFourTranslationImage_ne_bot
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U))
    (hretained : ¬ E block P ≤ N.1) :
    degreeFourTranslationImage block P N ≠ ⊥ := by
  intro hbot
  apply hretained
  have hle : E block P ≤ (QuotientGroup.mk' N.1).ker :=
    (Subgroup.map_eq_bot_iff
      (H := E block P) (f := QuotientGroup.mk' N.1)).mp hbot
  simpa only [QuotientGroup.ker_mk'] using hle

/-- The literal local translation space in affine degree four has
characteristic two and dimension two. -/
theorem degreeFour_translationDimension
    (hr : Nat.card block.Fibre = 4) :
    P.p = 2 ∧ (chart block P).d = 2 := by
  let C := chart block P
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V ↦ C.equiv.symm (Multiplicative.ofAdd v))
    C.equiv.symm.injective
  have hdegree : 4 = P.p ^ C.d := by
    rw [← hr]
    simpa [PrimitiveAffineProfile.ElementaryChart.d] using
      P.degree_eq_prime_pow_finrank C.equiv (origin block)
  exact prime_pow_positive_injective (d := C.d) (e := 2)
    P.p_prime Nat.prime_two C.d_pos (by norm_num)
      (hdegree.symm.trans (by norm_num))

/-- The actual correlated degree-four translation intersection has exponent
two. -/
theorem degreeFour_translation_pow_two
    (hr : Nat.card block.Fibre = 4) (x : E block P) : x ^ 2 = 1 := by
  apply (translationMulEquiv block P).injective
  apply Multiplicative.toAdd.injective
  simp only [map_pow, map_one, toAdd_pow, toAdd_one]
  change 2 • ((translationMulEquiv block P x).toAdd) = 0
  rw [← (degreeFour_translationDimension block P hr).1]
  exact ZModModule.char_nsmul_eq_zero P.p _

/-- Every retained image of the actual translation intersection still has
exponent two. -/
theorem degreeFourTranslationImage_pow_two
    (hr : Nat.card block.Fibre = 4)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U))
    (x : degreeFourTranslationImage block P N) : x ^ 2 = 1 := by
  let q := QuotientGroup.mk' N.1
  let f : E block P →* degreeFourTranslationImage block P N :=
    q.subgroupMap (E block P)
  obtain ⟨x₀, rfl⟩ := MonoidHom.subgroupMap_surjective q (E block P) x
  rw [← map_pow, degreeFour_translation_pow_two block P hr, map_one]

/-- A translation-carried normal section with zero complete binary head is
absorbed by the actual ambient commutator.  This is the quotient-section
form consumed after the retained-annihilator chain has proved head zero. -/
theorem degreeFour_translationSection_commutator_full_of_relativeHead_zero
    (hr : Nat.card block.Fibre = 4)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U))
    (M : Subgroup (DegreeFourRetainedQuotient N)) [M.Normal]
    (hM : M ≤ degreeFourTranslationImage block P N)
    (hzero : Module.finrank (ZMod 2)
      (primeRelativeCharacters 2 M) = 0) :
    ⁅M, (⊤ : Subgroup (DegreeFourRetainedQuotient N))⁆ = M := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  apply mixedCommutator_eq_of_exponent_prime_relativeHead_zero 2 M
  · intro m
    let x : degreeFourTranslationImage block P N := ⟨m.1, hM m.2⟩
    apply Subtype.ext
    change (m.1 : DegreeFourRetainedQuotient N) ^ 2 = 1
    exact congrArg Subtype.val
      (degreeFourTranslationImage_pow_two block P hr N x)
  · exact hzero

/-- The preimage of the correlated ternary core has abelian quotient by
the literal translation intersection. -/
theorem degreeFourTernaryPreimage_commutator_le_translation
    (hr : Nat.card block.Fibre = 4) :
    ⁅degreeFourTernaryPreimage block P,
        degreeFourTernaryPreimage block P⁆ ≤ E block P := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  apply (QuotientGroup.eq_one_iff ⁅x, y⁆).mp
  change QuotientGroup.mk' (E block P) ⁅x, y⁆ = 1
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr
    (congrArg Subtype.val
      (degreeFourTernaryCore_commute block P hr
        ⟨QuotientGroup.mk' (E block P) x, hx⟩
        ⟨QuotientGroup.mk' (E block P) y, hy⟩).eq)

/-- Hence the image `barB` in every retained quotient is abelian modulo
the image `barE`. -/
theorem degreeFourTernaryPreimageImage_commutator_le_translationImage
    (hr : Nat.card block.Fibre = 4)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    ⁅degreeFourTernaryPreimageImage block P N,
        degreeFourTernaryPreimageImage block P N⁆ ≤
      degreeFourTranslationImage block P N := by
  rw [← Subgroup.map_commutator]
  exact Subgroup.map_mono
    (degreeFourTernaryPreimage_commutator_le_translation block P hr)

/-- The part of the quotient socle on which `barB` acts nontrivially. -/
abbrev degreeFourCoreActiveSoclePart
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    Subgroup (DegreeFourRetainedQuotient N) :=
  nontrivialActionSoclePart (DegreeFourRetainedQuotient N)
    (degreeFourTernaryPreimageImage block P N)

/-- The complementary part on which `barB` acts trivially. -/
abbrev degreeFourCoreFixedSoclePart
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    Subgroup (DegreeFourRetainedQuotient N) :=
  trivialActionSoclePart (DegreeFourRetainedQuotient N)
    (degreeFourTernaryPreimageImage block P N)

/-- The remaining representation-theoretic statement in the nonzero-core
degree-four route, phrased only for ambient minimal normal factors of the
literal retained quotient.  It says that the core acts nontrivially exactly
on the factors physically carried by the actual translation image. -/
def DegreeFourFaithfulCoreSection
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) : Prop :=
  ∀ M : Subgroup (DegreeFourRetainedQuotient N),
    IsMinimalNormalSubgroup M →
      (⁅degreeFourTernaryPreimageImage block P N, M⁆ = M ↔
        M ≤ degreeFourTranslationImage block P N)

/-- The core action split is intrinsically a disjoint-type split.  Thus the
maximum sharing of normal-generator slots never needs an abstract list of
simple types. -/
theorem degreeFourCoreAction_noCommonNormalQuotient
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    NoCommonNormalQuotient
      (degreeFourCoreActiveSoclePart block P N)
      (degreeFourCoreFixedSoclePart block P N) :=
  noCommonNormalQuotient_actionSocleParts
    (DegreeFourRetainedQuotient N)
    (degreeFourTernaryPreimageImage block P N)

/-- Every ambient minimal normal factor on which `barB` acts nontrivially
is physically carried by `barE`.  The proof uses only normality and the
already-proved fact that `barB/barE` is abelian. -/
theorem degreeFourCoreActiveSoclePart_le_translationImage
    (hr : Nat.card block.Fibre = 4)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    degreeFourCoreActiveSoclePart block P N ≤
      degreeFourTranslationImage block P N := by
  unfold degreeFourCoreActiveSoclePart nontrivialActionSoclePart
    minimalNormalSoclePart
  apply Finset.sup_le
  intro M hM
  have hfull :
      ⁅degreeFourTernaryPreimageImage block P N, M⁆ = M :=
    (Finset.mem_filter.mp hM).2.2
  have hMB : M ≤ degreeFourTernaryPreimageImage block P N := by
    rw [← hfull]
    exact Subgroup.commutator_le_left _ _
  rw [← hfull]
  exact (Subgroup.commutator_mono le_rfl hMB).trans
    (degreeFourTernaryPreimageImage_commutator_le_translationImage
      block P hr N)

/-- The forward half of the faithful-core statement is automatic from the
literal extension `barE ◁ barB` with abelian quotient: every active ambient
minimal factor is translation-carried. -/
theorem degreeFour_minimalNormal_active_le_translationImage
    (hr : Nat.card block.Fibre = 4)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U))
    (M : Subgroup (DegreeFourRetainedQuotient N))
    (hactive :
      ⁅degreeFourTernaryPreimageImage block P N, M⁆ = M) :
    M ≤ degreeFourTranslationImage block P N := by
  have hMB : M ≤ degreeFourTernaryPreimageImage block P N := by
    rw [← hactive]
    exact Subgroup.commutator_le_left _ _
  rw [← hactive]
  exact (Subgroup.commutator_mono le_rfl hMB).trans
    (degreeFourTernaryPreimageImage_commutator_le_translationImage
      block P hr N)

/-- Thus the full faithful-core theorem is equivalent to its genuinely
substantive half: every translation-carried ambient minimal factor is
nontrivial under the retained ternary core. -/
theorem degreeFourFaithfulCoreSection_iff_translation_active
    (hr : Nat.card block.Fibre = 4)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    DegreeFourFaithfulCoreSection block P N ↔
      ∀ M : Subgroup (DegreeFourRetainedQuotient N),
        IsMinimalNormalSubgroup M →
        M ≤ degreeFourTranslationImage block P N →
          ⁅degreeFourTernaryPreimageImage block P N, M⁆ = M := by
  constructor
  · intro h M hM hME
    exact (h M hM).2 hME
  · intro h M hM
    constructor
    · exact degreeFour_minimalNormal_active_le_translationImage
        block P hr N M
    · exact h M hM

/-- The nonzero literal ternary core is faithful on every surviving
translation-carried ambient minimal factor.  If such a factor were
centralized, a nonidentity element would give a nonzero vector fixed modulo
the exact invariant intersection `N ∩ E`.  The coprime Maschke lemma above
lifts that vector to an original fixed vector, contradicting the concrete
coordinate calculation. -/
theorem degreeFourFaithfulCoreSection_of_nonzero
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P ≠ ⊥)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    DegreeFourFaithfulCoreSection block P N := by
  rw [degreeFourFaithfulCoreSection_iff_translation_active block P hr N]
  intro M hM hME
  letI : M.Normal := hM.1
  rcases minimalNormal_commutator_full_or_trivial
      (degreeFourTernaryPreimageImage block P N) M hM with hfull | hcommzero
  · exact hfull
  · exfalso
    obtain ⟨m, hmne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hM.2.1
    obtain ⟨e, heE, he⟩ := hME m.2
    let ee : E block P := ⟨e, heE⟩
    let C := elementaryChart block P
    let v : C.V := (C.equiv ee).toAdd
    have hv : v ∉
        C.originalKernelChart.normalSubrepresentation
          (QuotientGroup.mk' (E block P))
          (QuotientGroup.mk'_surjective (E block P))
          C.quotientRepresentation N.1 := by
      intro hvI
      have heN : e ∈ N.1 :=
        (degreeFive_elementaryChart_mem_normalSubrepresentation_iff
          block P N ee).1 hvI
      apply hmne
      apply Subtype.ext
      rw [← he]
      exact (QuotientGroup.eq_one_iff e).2 heN
    have hfixedMod : ∀ d : degreeFourTernaryCore block P,
        degreeFourTernaryAction block P d v - v ∈
          C.originalKernelChart.normalSubrepresentation
            (QuotientGroup.mk' (E block P))
            (QuotientGroup.mk'_surjective (E block P))
            C.quotientRepresentation N.1 := by
      intro d
      obtain ⟨g, hg⟩ :=
        QuotientGroup.mk'_surjective (E block P) d.1
      have hgB : g ∈ degreeFourTernaryPreimage block P := by
        change QuotientGroup.mk' (E block P) g ∈
          degreeFourTernaryCore block P
        rw [hg]
        exact d.2
      have hqgB : QuotientGroup.mk' N.1 g ∈
          degreeFourTernaryPreimageImage block P N :=
        ⟨g, hgB, rfl⟩
      have hqeM : QuotientGroup.mk' N.1 e ∈ M := by
        rw [he]
        exact m.2
      have hcentral : degreeFourTernaryPreimageImage block P N ≤
          Subgroup.centralizer (M : Set (DegreeFourRetainedQuotient N)) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommzero
      have hcommute : Commute (QuotientGroup.mk' N.1 e)
          (QuotientGroup.mk' N.1 g) :=
        Subgroup.mem_centralizer_iff.mp (hcentral hqgB) _ hqeM
      let k : E block P := MulAut.conjNormal g ee * ee⁻¹
      have hkN : (k.1 : preE7NonPairAction w U) ∈ N.1 := by
        apply (QuotientGroup.eq_one_iff k.1).mp
        change QuotientGroup.mk' N.1 (g * e * g⁻¹ * e⁻¹) = 1
        simp only [map_mul, map_inv]
        rw [hcommute.eq.symm]
        simp
      have hkI : (C.equiv k).toAdd ∈
          C.originalKernelChart.normalSubrepresentation
            (QuotientGroup.mk' (E block P))
            (QuotientGroup.mk'_surjective (E block P))
            C.quotientRepresentation N.1 :=
        (degreeFive_elementaryChart_mem_normalSubrepresentation_iff
          block P N k).2 hkN
      have haction := C.quotientRepresentation_apply g ee
      have hkcoord : (C.equiv k).toAdd =
          degreeFourTernaryAction block P d v - v := by
        change (C.equiv (MulAut.conjNormal g ee * ee⁻¹)).toAdd = _
        unfold degreeFourTernaryAction
        rw [map_mul, map_inv, toAdd_mul, toAdd_inv, ← haction, hg]
        dsimp only [C, v]
        simp only [sub_eq_add_neg]
      rw [← hkcoord]
      exact hkI
    exact degreeFour_no_fixed_vector_mod_normalSubrepresentation
      block P hTraceyPerm hr hD N.1 v hv hfixedMod

/-- The actual global translation intersection retains its correlations but
still injects into the product of the literal four-point translation
groups. -/
theorem degreeFourTranslationIntersection_card_le
    (hr : Nat.card block.Fibre = 4) :
    Nat.card (E block P) ≤ 4 ^ Nat.card block.Points := by
  letI : Finite (chart block P).V := Finite.of_injective
    (fun v : (chart block P).V ↦
      (chart block P).equiv.symm (Multiplicative.ofAdd v))
    (chart block P).equiv.symm.injective
  have hV : Nat.card (chart block P).V = 4 := by
    calc
      Nat.card (chart block P).V =
          Nat.card (Multiplicative (chart block P).V) := rfl
      _ = Nat.card P.V := Nat.card_congr (chart block P).equiv.symm.toEquiv
      _ = Nat.card block.Fibre := P.card_eq (origin block)
      _ = 4 := hr
  calc
    Nat.card (E block P) ≤
        Nat.card (Multiplicative
          (block.Points → (chart block P).V)) :=
      Nat.card_le_card_of_injective (coordinates block P)
        (coordinates_injective block P)
    _ = Nat.card (block.Points → (chart block P).V) := rfl
    _ = Nat.card (chart block P).V ^ Nat.card block.Points := by
      rw [Nat.card_fun]
    _ = 4 ^ Nat.card block.Points := by rw [hV]

/-- Passing to a literal retained quotient cannot enlarge its translation
image. -/
theorem degreeFourTranslationImage_card_le
    (hr : Nat.card block.Fibre = 4)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    Nat.card (degreeFourTranslationImage block P N) ≤
      4 ^ Nat.card block.Points := by
  exact (Nat.card_le_card_of_surjective
    ((QuotientGroup.mk' N.1).subgroupMap (E block P))
    (MonoidHom.subgroupMap_surjective _ _)).trans
      (degreeFourTranslationIntersection_card_le block P hr)

/-- The core-active socle part has the same physical cardinal ceiling. -/
theorem degreeFourCoreActiveSoclePart_card_le
    (hr : Nat.card block.Fibre = 4)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    Nat.card (degreeFourCoreActiveSoclePart block P N) ≤
      4 ^ Nat.card block.Points :=
  (Subgroup.card_le_of_le
    (degreeFourCoreActiveSoclePart_le_translationImage block P hr N)).trans
      (degreeFourTranslationImage_card_le block P hr N)

private theorem four_pow_le_sixteen_pow_ceiling_half
    (s : ℕ) : 4 ^ s ≤ 16 ^ ((s + 1) / 2) := by
  rw [show 4 = 2 ^ (2 : ℕ) by norm_num,
    show 16 = 2 ^ (4 : ℕ) by norm_num, ← pow_mul, ← pow_mul]
  apply Nat.pow_le_pow_right (by norm_num)
  omega

/-- The whole quotient socle is split canonically by its action under the
literal `barB`, and distinct action types share tuple positions by the
generic ambient Goursat theorem. -/
theorem degreeFour_socle_normalGen_le_max_coreActionParts
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    MarkedC4.normalGen (finiteGroupSocle (DegreeFourRetainedQuotient N)) ≤
      max
        (MarkedC4.normalGen (degreeFourCoreActiveSoclePart block P N))
        (MarkedC4.normalGen (degreeFourCoreFixedSoclePart block P N)) :=
  normalGen_finiteGroupSocle_le_max_actionSocleParts
    (DegreeFourRetainedQuotient N)
    (degreeFourTernaryPreimageImage block P N)

/-- The ambient-minimal factors carried by `barE`. -/
abbrev degreeFourTranslationSoclePart
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    Subgroup (DegreeFourRetainedQuotient N) :=
  minimalNormalSoclePart (DegreeFourRetainedQuotient N)
    (fun M ↦ M ≤ degreeFourTranslationImage block P N)

/-- The complementary ambient-minimal factors, i.e. those not carried by
the translation image. -/
abbrev degreeFourCoreTrivialSoclePart
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    Subgroup (DegreeFourRetainedQuotient N) :=
  minimalNormalSoclePart (DegreeFourRetainedQuotient N)
    (fun M ↦ ¬ M ≤ degreeFourTranslationImage block P N)

/-- Under the faithful-core-section theorem, the action-active part is the
literal translation-carried socle part. -/
theorem degreeFourCoreActiveSoclePart_eq_translationSoclePart
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U))
    (hfaithful : DegreeFourFaithfulCoreSection block P N) :
    degreeFourCoreActiveSoclePart block P N =
      degreeFourTranslationSoclePart block P N :=
  minimalNormalSoclePart_congr
    (DegreeFourRetainedQuotient N)
    (fun M ↦ ⁅degreeFourTernaryPreimageImage block P N, M⁆ = M)
    (fun M ↦ M ≤ degreeFourTranslationImage block P N)
    hfaithful

/-- The action-fixed part is then precisely the complementary outer-type
socle sum. -/
theorem degreeFourCoreFixedSoclePart_eq_coreTrivialSoclePart
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U))
    (hfaithful : DegreeFourFaithfulCoreSection block P N) :
    degreeFourCoreFixedSoclePart block P N =
      degreeFourCoreTrivialSoclePart block P N := by
  apply minimalNormalSoclePart_congr
  intro M hM
  exact not_congr (hfaithful M hM)

/-- The two literal parts cover the whole socle of `Q`. -/
theorem degreeFourSocleParts_sup_eq
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    degreeFourTranslationSoclePart block P N ⊔
        degreeFourCoreTrivialSoclePart block P N =
      finiteGroupSocle (DegreeFourRetainedQuotient N) :=
  minimalNormalSoclePart_sup_compl_eq_finiteGroupSocle
    (DegreeFourRetainedQuotient N)
    (fun M ↦ M ≤ degreeFourTranslationImage block P N)

/-- The cardinal theorem for an actual translation-carried socle part.  In
the degree-four proof the eventual parameters are supplied by the physical
binary-module calculation; this lemma ensures that calculation is applied
to ambient minimal factors rather than to intrinsic order-two subgroups of
`barE`. -/
theorem degreeFourTranslationSoclePart_normalGen_le_of_card
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U))
    (m t : ℕ) (hm : 2 ≤ m)
    (hmin : ∀ M : Subgroup (DegreeFourRetainedQuotient N),
      IsMinimalNormalSubgroup M →
      M ≤ degreeFourTranslationImage block P N → m ≤ Nat.card M)
    (hcard : Nat.card (degreeFourTranslationImage block P N) ≤ m ^ t) :
    MarkedC4.normalGen (degreeFourTranslationSoclePart block P N) ≤ t := by
  exact normalGen_finiteGroupSoclePart_le_of_card
    (DegreeFourRetainedQuotient N)
    (degreeFourTranslationImage block P N) m t hm hmin hcard

/-- Type-sharing converts sharp bounds on the two actual socle parts into
the whole-socle bound required by Zmud.  The `NoCommonNormalQuotient`
premise is discharged below from the `D`-action; it is exposed here so the
normal-generator arithmetic is independent of that quotient transport. -/
theorem degreeFour_socle_normalGen_le_slots_of_typeSharing
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U))
    (slots : ℕ)
    (hNoCommon : NoCommonNormalQuotient
      (degreeFourTranslationSoclePart block P N)
      (degreeFourCoreTrivialSoclePart block P N))
    (htranslation : MarkedC4.normalGen
      (degreeFourTranslationSoclePart block P N) ≤ slots)
    (htop : MarkedC4.normalGen
      (degreeFourCoreTrivialSoclePart block P N) ≤ slots) :
    MarkedC4.normalGen (finiteGroupSocle (DegreeFourRetainedQuotient N)) ≤
      slots := by
  rw [← degreeFourSocleParts_sup_eq block P N]
  exact (normalGen_sup_le_max_of_noCommonNormalQuotient _ _ hNoCommon).trans
    (max_le htranslation htop)

/-- Exact padded-tuple form of the preceding actual-frame theorem. -/
noncomputable def degreeFour_socleNormalGeneratorBound_of_typeSharing
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U))
    (slots : ℕ)
    (hNoCommon : NoCommonNormalQuotient
      (degreeFourTranslationSoclePart block P N)
      (degreeFourCoreTrivialSoclePart block P N))
    (htranslation : MarkedC4.normalGen
      (degreeFourTranslationSoclePart block P N) ≤ slots)
    (htop : MarkedC4.normalGen
      (degreeFourCoreTrivialSoclePart block P N) ≤ slots) :
    SocleNormalGeneratorBound (DegreeFourRetainedQuotient N) slots :=
  (socleNormalGeneratorBound_iff_normalGen_le
    (DegreeFourRetainedQuotient N) slots).2
      (degreeFour_socle_normalGen_le_slots_of_typeSharing block P N slots
        hNoCommon htranslation htop)

/-- Construction-facing whole-socle tuple after the actual faithful-core
section statement and the two literal part bounds have been proved.  The
type-sharing premise is discharged by the core action itself. -/
noncomputable def degreeFour_socleNormalGeneratorBound_of_faithfulCoreSection
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U))
    (slots : ℕ)
    (hfaithful : DegreeFourFaithfulCoreSection block P N)
    (htranslation : MarkedC4.normalGen
      (degreeFourTranslationSoclePart block P N) ≤ slots)
    (htop : MarkedC4.normalGen
      (degreeFourCoreTrivialSoclePart block P N) ≤ slots) :
    SocleNormalGeneratorBound (DegreeFourRetainedQuotient N) slots := by
  apply (socleNormalGeneratorBound_iff_normalGen_le
    (DegreeFourRetainedQuotient N) slots).2
  refine (degreeFour_socle_normalGen_le_max_coreActionParts block P N).trans ?_
  rw [degreeFourCoreActiveSoclePart_eq_translationSoclePart
      block P N hfaithful,
    degreeFourCoreFixedSoclePart_eq_coreTrivialSoclePart
      block P N hfaithful]
  exact max_le htranslation htop

/-! ## Quotient sections which are trivial on the ternary core

This is the missing quotient-transfer step in the paper proof.  Let
`L ◁ R` and let `A ◁ R/L` be a socle part which centralizes, and is
disjoint from, the image of `D`.  Its full inverse image `H` centralizes
`D` already in `R`: every commutator lies both in `L` and in `D`, while
`L ∩ D = 1`.  The same argument makes `H ∩ D` trivial.  The concrete
centralizer identity above then embeds `H` in the actual block top.

All statements are phrased for the literal quotient map.  This avoids the
invalid shortcut of treating an affine component as a new pre-`E7` action.
-/

/-- Full inverse image in `R` of a chosen subgroup of `R/L`. -/
abbrev degreeFourCoreTrivialSectionPreimage
    (L : Subgroup (DegreeFourComplementQuotient block P)) [L.Normal]
    (A : Subgroup (DegreeFourComplementQuotient block P ⧸ L)) :
    Subgroup (DegreeFourComplementQuotient block P) :=
  A.comap (QuotientGroup.mk' L)

instance degreeFourCoreTrivialSectionPreimage_normal
    (L : Subgroup (DegreeFourComplementQuotient block P)) [L.Normal]
    (A : Subgroup (DegreeFourComplementQuotient block P ⧸ L))
    [A.Normal] :
    (degreeFourCoreTrivialSectionPreimage block P L A).Normal := by
  dsimp only [degreeFourCoreTrivialSectionPreimage]
  infer_instance

/-- Centrality modulo `L` puts the lifted commutator in `L`. -/
theorem degreeFourCoreTrivialSectionPreimage_commutator_le
    (L : Subgroup (DegreeFourComplementQuotient block P)) [L.Normal]
    (A : Subgroup (DegreeFourComplementQuotient block P ⧸ L))
    (hcentral : A ≤ Subgroup.centralizer
      ((degreeFourTernaryCore block P).map (QuotientGroup.mk' L) :
        Set (DegreeFourComplementQuotient block P ⧸ L))) :
    ⁅degreeFourCoreTrivialSectionPreimage block P L A,
        degreeFourTernaryCore block P⁆ ≤ L := by
  rw [Subgroup.commutator_le]
  intro h hh d hd
  apply (QuotientGroup.eq_one_iff ⁅h, d⁆).mp
  change QuotientGroup.mk' L ⁅h, d⁆ = 1
  rw [map_commutatorElement]
  apply commutatorElement_eq_one_iff_mul_comm.mpr
  have hhCentral := hcentral hh
  exact (Subgroup.mem_centralizer_iff.mp hhCentral
    (QuotientGroup.mk' L d) ⟨d, hd, rfl⟩).symm

/-- Disjointness modulo `L` puts the lifted intersection in `L`. -/
theorem degreeFourCoreTrivialSectionPreimage_inf_core_le
    (L : Subgroup (DegreeFourComplementQuotient block P)) [L.Normal]
    (A : Subgroup (DegreeFourComplementQuotient block P ⧸ L))
    (hdisjoint : A ⊓
      (degreeFourTernaryCore block P).map (QuotientGroup.mk' L) = ⊥) :
    degreeFourCoreTrivialSectionPreimage block P L A ⊓
        degreeFourTernaryCore block P ≤ L := by
  rintro x ⟨hxA, hxD⟩
  apply (QuotientGroup.eq_one_iff x).mp
  have hxInf : QuotientGroup.mk' L x ∈
      A ⊓ (degreeFourTernaryCore block P).map (QuotientGroup.mk' L) :=
    ⟨hxA, ⟨x, hxD, rfl⟩⟩
  rw [hdisjoint] at hxInf
  exact Subgroup.mem_bot.mp hxInf

/-- The lifted section centralizes `D` and is disjoint from it whenever the
kernel `L` is.  This packages the two elementary intersection arguments
without invoking any classification theorem. -/
theorem degreeFourCoreTrivialSectionPreimage_centralizes_disjoint
    (L : Subgroup (DegreeFourComplementQuotient block P)) [L.Normal]
    (A : Subgroup (DegreeFourComplementQuotient block P ⧸ L)) [A.Normal]
    (hLD : L ⊓ degreeFourTernaryCore block P = ⊥)
    (hcentral : A ≤ Subgroup.centralizer
      ((degreeFourTernaryCore block P).map (QuotientGroup.mk' L) :
        Set (DegreeFourComplementQuotient block P ⧸ L)))
    (hdisjoint : A ⊓
      (degreeFourTernaryCore block P).map (QuotientGroup.mk' L) = ⊥) :
    degreeFourCoreTrivialSectionPreimage block P L A ≤
        Subgroup.centralizer
          (degreeFourTernaryCore block P :
            Set (DegreeFourComplementQuotient block P)) ∧
      degreeFourCoreTrivialSectionPreimage block P L A ⊓
        degreeFourTernaryCore block P = ⊥ := by
  have hcommL := degreeFourCoreTrivialSectionPreimage_commutator_le
    block P L A hcentral
  have hcommD :
      ⁅degreeFourCoreTrivialSectionPreimage block P L A,
        degreeFourTernaryCore block P⁆ ≤ degreeFourTernaryCore block P :=
    Subgroup.commutator_le_right _ _
  have hcommBot :
      ⁅degreeFourCoreTrivialSectionPreimage block P L A,
        degreeFourTernaryCore block P⁆ = ⊥ := by
    apply le_bot_iff.mp
    have hle :
        ⁅degreeFourCoreTrivialSectionPreimage block P L A,
          degreeFourTernaryCore block P⁆ ≤
            L ⊓ degreeFourTernaryCore block P :=
      le_inf hcommL hcommD
    simpa only [hLD] using hle
  have hcentralLift :
      degreeFourCoreTrivialSectionPreimage block P L A ≤
        Subgroup.centralizer
          (degreeFourTernaryCore block P :
            Set (DegreeFourComplementQuotient block P)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommBot
  have hinfL := degreeFourCoreTrivialSectionPreimage_inf_core_le
    block P L A hdisjoint
  have hinfBot : degreeFourCoreTrivialSectionPreimage block P L A ⊓
      degreeFourTernaryCore block P = ⊥ := by
    apply le_bot_iff.mp
    have hle : degreeFourCoreTrivialSectionPreimage block P L A ⊓
        degreeFourTernaryCore block P ≤
          L ⊓ degreeFourTernaryCore block P :=
      le_inf hinfL inf_le_right
    simpa only [hLD] using hle
  exact ⟨hcentralLift, hinfBot⟩

/-- A core-trivial quotient section embeds in the actual block top.  This is
the formal `H/L ↪ T` bridge, with `H` first embedded and then quotiented;
the present theorem records the stronger injection of `H`, which is what
the subsequent cardinal and sectional-rank bounds consume. -/
theorem degreeFourCoreTrivialSectionPreimage_top_injective
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P ≠ ⊥)
    (L : Subgroup (DegreeFourComplementQuotient block P)) [L.Normal]
    (A : Subgroup (DegreeFourComplementQuotient block P ⧸ L)) [A.Normal]
    (hLD : L ⊓ degreeFourTernaryCore block P = ⊥)
    (hcentral : A ≤ Subgroup.centralizer
      ((degreeFourTernaryCore block P).map (QuotientGroup.mk' L) :
        Set (DegreeFourComplementQuotient block P ⧸ L)))
    (hdisjoint : A ⊓
      (degreeFourTernaryCore block P).map (QuotientGroup.mk' L) = ⊥) :
    Function.Injective
      (degreeFourRestrictedTopMap block P
        (degreeFourCoreTrivialSectionPreimage block P L A)) := by
  obtain ⟨hcentralLift, hdisjointLift⟩ :=
    degreeFourCoreTrivialSectionPreimage_centralizes_disjoint
      block P L A hLD hcentral hdisjoint
  exact degreeFourRestrictedTopMap_injective_of_centralizes_disjoint
    block P hr hD _ hcentralLift hdisjointLift


end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
