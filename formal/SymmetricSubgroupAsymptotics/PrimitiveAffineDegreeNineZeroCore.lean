import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeNineWholeCore
import SymmetricSubgroupAsymptotics.ElementaryNormalModuleGenerators
import SymmetricSubgroupAsymptotics.NonabelianSoclePartCenterless
import SymmetricSubgroupAsymptotics.NonPrimeAbelianSoclePart
import SymmetricSubgroupAsymptotics.PermutationSectionNormalGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineTranslationLayerSource

/-!
# The zero-core degree-nine ternary filtration

When the whole actual linear block kernel vanishes, the quotient above the
retained translation image is a literal
section of the transitive block top.  This file proves the outer half of the
manuscript filtration without replacing the original block system: the image
of the whole ternary socle costs at most `floor(s/3)` normal generators.

The proof first keeps the exact whole retained core and only rewrites it to
the translation image after the zero-kernel branch has been selected.
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
  [Nontrivial block.Fibre]

/-! ## Normal subgroups carried by the literal retained top -/

/-- Any ambient normal subgroup disjoint from the retained affine core is
faithfully carried by a quotient section of the original block top.  The
published permutation-subgroup generator bound therefore gives `s` normal
generators, uniformly across abelian and nonabelian socle types. -/
theorem degreeNineCoreDisjoint_normalGen_le
    (hgen : PermutationSubgroupGeneratorBound)
    (hs : 2 ≤ Nat.card block.Points)
    (N : LiteralNormalAxis (preE7NonPairAction w U))
    (H : Subgroup (preE7NonPairAction w U ⧸ N.1)) [H.Normal]
    (hdisjoint : H ⊓ degreeNineWholeRetainedCore block P N = ⊥) :
    MarkedC4.normalGen H ≤ Nat.card block.Points := by
  exact degreeNineWholeCoreDisjoint_normalGen_le block P hgen hs N H
    hdisjoint

/-- The retained translation image is a ternary group. -/
theorem degreeNineTranslationImage_isPGroup
    (hr : Nat.card block.Fibre = 9)
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    IsPGroup 3 (degreeNineTranslationImage block P N) := by
  intro x
  refine ⟨1, ?_⟩
  simpa using degreeNineTranslationImage_pow_three block P hr N x

/-- Prime-power subgroups of coprime characteristics intersect trivially. -/
private theorem primePowerSubgroups_inf_eq_bot_of_coprime
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

/-- The least ambient normal-generator number is invariant under a group
equivalence.  Keeping this elementary transport explicit avoids dependent
rewriting between quotient groups formed from propositionally equal normal
subgroups. -/
private theorem normalGen_map_mulEquiv_eq
    {G H : Type} [Group G] [Finite G] [Group H] [Finite H]
    (e : G ≃* H) (K : Subgroup G) [K.Normal] :
    MarkedC4.normalGen (K.map e.toMonoidHom) =
      MarkedC4.normalGen K := by
  apply le_antisymm
  · exact MarkedC4.normalGen_map_le e.toMonoidHom e.surjective K
  · letI : (K.map e.toMonoidHom).Normal :=
      Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
    have hback := MarkedC4.normalGen_map_le e.symm.toMonoidHom
      e.symm.surjective (K.map e.toMonoidHom)
    have hreturn :
        (K.map e.toMonoidHom).map e.symm.toMonoidHom = K := by
      ext x
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        simpa using hz
      · intro hx
        exact ⟨e x, ⟨x, hx, rfl⟩, e.symm_apply_apply x⟩
    simpa only [hreturn] using hback

/-- One nonternary prime-primary piece of the degree-nine socle. -/
abbrev degreeNineNonTernaryPrimeSoclePart
    (p : ℕ)
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    Subgroup (preE7NonPairAction w U ⧸ N.1) :=
  minimalNormalSoclePart (preE7NonPairAction w U ⧸ N.1)
    (fun M => ¬ IsPGroup 3 M ∧ IsPGroup p M)

theorem degreeNineNonTernaryPrimeSoclePart_isPGroup
    (p : ℕ) [Fact p.Prime]
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    IsPGroup p (degreeNineNonTernaryPrimeSoclePart p N) :=
  primePrimarySoclePart_isPGroup_of_predicate p
    (preE7NonPairAction w U ⧸ N.1) (fun M => ¬ IsPGroup 3 M)

/-- In the zero-core branch every nonternary prime-primary piece is
disjoint from the retained core and is therefore carried by the literal
permutation-top section. -/
theorem degreeNineZeroCore_nonTernaryPrime_normalGen_le
    (hgen : PermutationSubgroupGeneratorBound)
    (hs : 2 ≤ Nat.card block.Points)
    (hr : Nat.card block.Fibre = 9)
    (hK : degreeNineLinearBlockKernel block P = ⊥)
    (p : ℕ) [Fact p.Prime] (hp3 : Nat.Coprime p 3)
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    MarkedC4.normalGen
        (degreeNineNonTernaryPrimeSoclePart p N) ≤
      Nat.card block.Points := by
  have hD : degreeNineWholeRetainedCore block P N =
      degreeNineTranslationImage block P N :=
    degreeNineWholeRetainedCore_eq_translationImage_of_kernel_eq_bot
      block P N hK
  apply degreeNineCoreDisjoint_normalGen_le block P hgen hs N
    (degreeNineNonTernaryPrimeSoclePart p N)
  rw [hD]
  exact primePowerSubgroups_inf_eq_bot_of_coprime p 3 hp3 _ _
    (degreeNineNonTernaryPrimeSoclePart_isPGroup p N)
    (degreeNineTranslationImage_isPGroup block P hr N)

/-- The entire nonabelian nonternary socle sum.  Unlike a prime-primary
piece, this sum can contain several simple types; centerlessness is the
uniform separator from the commutative translation core. -/
abbrev degreeNineNonTernaryNonabelianSoclePart
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    Subgroup (preE7NonPairAction w U ⧸ N.1) :=
  minimalNormalSoclePart (preE7NonPairAction w U ⧸ N.1)
    (fun M => ¬ IsPGroup 3 M ∧ ¬ IsMulCommutative M)

/-- In the zero-core branch all nonabelian nonternary minimal-normal
factors are carried simultaneously by the literal permutation top.  The
point is that their ambient socle sum is centerless, whereas the retained
translation image is commutative. -/
theorem degreeNineZeroCore_nonTernaryNonabelian_normalGen_le
    (hgen : PermutationSubgroupGeneratorBound)
    (hs : 2 ≤ Nat.card block.Points)
    (hr : Nat.card block.Fibre = 9)
    (hK : degreeNineLinearBlockKernel block P = ⊥)
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    MarkedC4.normalGen
        (degreeNineNonTernaryNonabelianSoclePart N) ≤
      Nat.card block.Points := by
  have hretained : degreeNineWholeRetainedCore block P N =
      degreeNineTranslationImage block P N :=
    degreeNineWholeRetainedCore_eq_translationImage_of_kernel_eq_bot
      block P N hK
  apply degreeNineCoreDisjoint_normalGen_le block P hgen hs N
    (degreeNineNonTernaryNonabelianSoclePart N)
  rw [hretained]
  letI : IsMulCommutative (degreeNineTranslationImage block P N) :=
    IsMulCommutative.of_comm fun x y =>
      (degreeNineTranslationImage_commute block P N x y).eq
  exact nonabelianMinimalNormalSoclePart_inf_commutativeNormal_eq_bot
    (G := preE7NonPairAction w U ⧸ N.1)
    (fun M => ¬ IsPGroup 3 M)
    (degreeNineTranslationImage block P N)
    (inferInstance : IsMulCommutative
      (degreeNineTranslationImage block P N))

/-- The entire abelian nonternary socle sum.  Its order is prime to three,
so it is disjoint from the retained ternary translation image without
splitting it into one theorem per auxiliary prime. -/
abbrev degreeNineNonTernaryAbelianSoclePart
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    Subgroup (preE7NonPairAction w U ⧸ N.1) :=
  minimalNormalSoclePart (preE7NonPairAction w U ⧸ N.1)
    (fun M => ¬ IsPGroup 3 M ∧ IsMulCommutative M)

/-- In the zero-core branch all abelian nonternary minimal-normal factors
are carried simultaneously by the literal permutation top. -/
theorem degreeNineZeroCore_nonTernaryAbelian_normalGen_le
    (hgen : PermutationSubgroupGeneratorBound)
    (hs : 2 ≤ Nat.card block.Points)
    (hr : Nat.card block.Fibre = 9)
    (hK : degreeNineLinearBlockKernel block P = ⊥)
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    MarkedC4.normalGen
        (degreeNineNonTernaryAbelianSoclePart N) ≤
      Nat.card block.Points := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hretained : degreeNineWholeRetainedCore block P N =
      degreeNineTranslationImage block P N :=
    degreeNineWholeRetainedCore_eq_translationImage_of_kernel_eq_bot
      block P N hK
  apply degreeNineCoreDisjoint_normalGen_le block P hgen hs N
    (degreeNineNonTernaryAbelianSoclePart N)
  rw [hretained]
  exact abelianNonPrimarySoclePart_inf_isPGroup_eq_bot 3
    (degreeNineTranslationImage block P N)
    (degreeNineTranslationImage_isPGroup block P hr N)

/-! ## The sharp translation-module generator bound -/

/-- Pull a normal subgroup of a retained quotient back inside the literal
translation intersection of the original action. -/
abbrev degreeNineTranslationPreimage
    (N : LiteralNormalAxis (preE7NonPairAction w U))
    (H : Subgroup (preE7NonPairAction w U ⧸ N.1)) :
    Subgroup (preE7NonPairAction w U) :=
  H.comap (QuotientGroup.mk' N.1) ⊓ E block P

instance degreeNineTranslationPreimage_normal
    (N : LiteralNormalAxis (preE7NonPairAction w U))
    (H : Subgroup (preE7NonPairAction w U ⧸ N.1)) [H.Normal] :
    (degreeNineTranslationPreimage block P N H).Normal := by
  dsimp only [degreeNineTranslationPreimage]
  infer_instance

theorem degreeNineTranslationPreimage_le_translation
    (N : LiteralNormalAxis (preE7NonPairAction w U))
    (H : Subgroup (preE7NonPairAction w U ⧸ N.1)) :
    degreeNineTranslationPreimage block P N H ≤ E block P :=
  inf_le_right

/-- If `H` lies in the retained translation image, its literal pullback
inside `E` maps onto exactly `H`. -/
theorem degreeNineTranslationPreimage_map_eq
    (N : LiteralNormalAxis (preE7NonPairAction w U))
    (H : Subgroup (preE7NonPairAction w U ⧸ N.1))
    (hH : H ≤ degreeNineTranslationImage block P N) :
    (degreeNineTranslationPreimage block P N H).map
        (QuotientGroup.mk' N.1) = H := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact hx.1
  · intro y hy
    have hyF := hH hy
    obtain ⟨e, heE, he⟩ := hyF
    refine ⟨e, ⟨?_, heE⟩, he⟩
    change QuotientGroup.mk' N.1 e ∈ H
    simpa only [he] using hy

/-- Tracey's published half-dimension theorem gives `s` module generators
for every invariant subspace of the actual correlated translation module:
the local module has dimension two and the actual block index is `s`. -/
theorem degreeNineTranslationAmbient_uniform
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 9)
    (i₀ : block.Points) :
    UniformSubrepresentationGeneratorBound
      (ActualWreathAffineCapacity.ambientRepresentation
        (initialState hTraceyPerm block) (localMap block P)
        (localTranslationChart block P))
      (Nat.card block.Points) := by
  let S := initialState hTraceyPerm block
  let C := localTranslationChart block P
  have hindex : 2 ≤ (S.topPointStabilizer i₀).index := by
    rw [S.topPointStabilizer_index i₀]
    simpa only [Fintype.card_eq_nat_card] using block.degrees_ge_two.2
  have hlocal := hTraceyHalf C.p S.A (S.topPointStabilizer i₀)
    hindex C.V
    (ActualWreathAffineCapacity.localRepresentation S
      (localMap block P) C i₀)
  have hambient := hlocal.of_injective
    (ActualWreathAffineCapacity.inducedIntertwiner S
      (localMap block P) C i₀)
    (ActualWreathAffineCapacity.inducedIntertwiner_injective S
      (localMap block P) C i₀)
  have hdim : Module.finrank (ZMod C.p) C.V = 2 := by
    simpa only [C, localTranslationChart, chart,
      PrimitiveAffineProfile.ElementaryChart.d] using
      (degreeNine_translationParameters block P hr).2
  have hbudget : 2 * Nat.card block.Points / 2 =
      Nat.card block.Points := by omega
  simpa only [S, C, hdim, S.topPointStabilizer_index i₀,
    Fintype.card_eq_nat_card, hbudget] using hambient

/-- Every translation-carried ambient socle part has the sharp `s`-slot
normal-generator bound.  The proof applies Tracey to its exact pullback in
the original correlated translation module and then maps the resulting
normal-generating tuple to the retained quotient. -/
theorem degreeNineTranslationCarried_normalGen_le
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 9)
    (i₀ : block.Points)
    (N : LiteralNormalAxis (preE7NonPairAction w U))
    (H : Subgroup (preE7NonPairAction w U ⧸ N.1)) [H.Normal]
    (hH : H ≤ degreeNineTranslationImage block P N) :
    MarkedC4.normalGen H ≤ Nat.card block.Points := by
  let L := degreeNineTranslationPreimage block P N H
  have hLgen : MarkedC4.normalGen L ≤ Nat.card block.Points := by
    apply normalGen_le_of_elementaryNormalSubrepresentation_comp_generated
      (E block P) (elementaryChart block P) L
      (degreeNineTranslationPreimage_le_translation block P N H)
    have huniform := degreeNineTranslationAmbient_uniform
      block P hTraceyHalf hTraceyPerm hr i₀
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
  rw [← degreeNineTranslationPreimage_map_eq block P N H hH]
  exact (MarkedC4.normalGen_map_le (QuotientGroup.mk' N.1)
    (QuotientGroup.mk'_surjective N.1) L).trans hLgen

/-- Specialization to the translation-selected socle sum. -/
theorem degreeNineTranslationSoclePart_normalGen_le_tracey
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 9)
    (i₀ : block.Points)
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    MarkedC4.normalGen (degreeNineTranslationSoclePart block P N) ≤
      Nat.card block.Points :=
  degreeNineTranslationCarried_normalGen_le block P hTraceyHalf hTraceyPerm
    hr i₀ N (degreeNineTranslationSoclePart block P N)
      (degreeNineTranslationSoclePart_le_image block P N)

/-- The whole ternary ambient socle part is a ternary group. -/
theorem degreeNineTernarySoclePart_isPGroup
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    IsPGroup 3 (degreeNineTernarySoclePart N) := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact minimalNormalSoclePart_isPGroup 3
    (preE7NonPairAction w U ⧸ N.1) (fun M => IsPGroup 3 M)
    (fun _ _ hM => hM)

/-- Image of the whole ternary socle after quotienting the retained actual
linear core. -/
abbrev degreeNineTernaryRetainedTopImage
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    Subgroup
      ((preE7NonPairAction w U ⧸ N.1) ⧸
        degreeNineWholeRetainedCore block P N) :=
  (degreeNineTernarySoclePart N).map
    (QuotientGroup.mk' (degreeNineWholeRetainedCore block P N))

instance degreeNineTernaryRetainedTopImage_normal
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    (degreeNineTernaryRetainedTopImage block P N).Normal :=
  Subgroup.Normal.map inferInstance
    (QuotientGroup.mk' (degreeNineWholeRetainedCore block P N))
    (QuotientGroup.mk'_surjective (degreeNineWholeRetainedCore block P N))

theorem degreeNineTernaryRetainedTopImage_isPGroup
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    IsPGroup 3 (degreeNineTernaryRetainedTopImage block P N) := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact (degreeNineTernarySoclePart_isPGroup N).map
    (QuotientGroup.mk' (degreeNineWholeRetainedCore block P N))

/-- The outer ternary filtration term inherits the sharp ternary sectional
rank of the literal block top. -/
theorem degreeNineTernaryRetainedTopImage_normalGen_le
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    MarkedC4.normalGen
        (degreeNineTernaryRetainedTopImage block P N) ≤
      Nat.card block.Points / 3 := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  refine (MarkedC4.normalGen_normalSubgroup_le_primeCharacterRank 3
    (degreeNineTernaryRetainedTopImage block P N)
    (degreeNineTernaryRetainedTopImage_isPGroup block P N)).trans ?_
  exact degreeNineWholeRetainedCoreQuotient_primeSectionalRank
    block P 3 N (degreeNineTernaryRetainedTopImage block P N)

/-- Zero local binary core identifies the preceding literal top image with
the quotient of the ternary socle by the retained translation image. -/
theorem degreeNineZeroCore_ternaryTopImage_normalGen_le
    (hr : Nat.card block.Fibre = 9)
    (hK : degreeNineLinearBlockKernel block P = ⊥)
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    MarkedC4.normalGen
        ((degreeNineTernarySoclePart N).map
          (QuotientGroup.mk' (degreeNineTranslationImage block P N))) ≤
      Nat.card block.Points / 3 := by
  have hD : degreeNineWholeRetainedCore block P N =
      degreeNineTranslationImage block P N :=
    degreeNineWholeRetainedCore_eq_translationImage_of_kernel_eq_bot
      block P N hK
  let e : ((preE7NonPairAction w U ⧸ N.1) ⧸
        degreeNineWholeRetainedCore block P N) ≃*
      ((preE7NonPairAction w U ⧸ N.1) ⧸
        degreeNineTranslationImage block P N) :=
    QuotientGroup.quotientMulEquivOfEq hD
  have he (x : preE7NonPairAction w U ⧸ N.1) :
      e (QuotientGroup.mk' (degreeNineWholeRetainedCore block P N) x) =
        QuotientGroup.mk' (degreeNineTranslationImage block P N) x :=
    QuotientGroup.quotientMulEquivOfEq_mk hD x
  let Kold := (degreeNineTernarySoclePart N).map
    (QuotientGroup.mk' (degreeNineWholeRetainedCore block P N))
  let Knew := (degreeNineTernarySoclePart N).map
    (QuotientGroup.mk' (degreeNineTranslationImage block P N))
  have himage : Kold.map e.toMonoidHom = Knew := by
    ext y
    constructor
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, (he x).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨QuotientGroup.mk'
        (degreeNineWholeRetainedCore block P N) x,
        ⟨x, hx, rfl⟩, he x⟩
  have hold : MarkedC4.normalGen Kold ≤ Nat.card block.Points / 3 :=
    degreeNineTernaryRetainedTopImage_normalGen_le block P N
  change MarkedC4.normalGen Knew ≤ Nat.card block.Points / 3
  rw [← himage, normalGen_map_mulEquiv_eq e Kold]
  exact hold

/-- Exact additive ternary filtration after the zero-core identification.
The inner term is left in its literal intersection form, ready for the
degree-nine homogeneous translation-module theorem. -/
theorem degreeNineZeroCore_ternary_normalGen_le_of_inner
    (hr : Nat.card block.Fibre = 9)
    (hK : degreeNineLinearBlockKernel block P = ⊥)
    (N : LiteralNormalAxis (preE7NonPairAction w U))
    (hinner : MarkedC4.normalGen
      (degreeNineTernarySoclePart N ⊓
        degreeNineTranslationImage block P N) ≤
          Nat.card block.Points) :
    MarkedC4.normalGen (degreeNineTernarySoclePart N) ≤
      Nat.card block.Points + Nat.card block.Points / 3 := by
  exact (MarkedC4.normalGen_normal_le_inter_add_image
      (degreeNineTernarySoclePart N)
      (degreeNineTranslationImage block P N)).trans
    (Nat.add_le_add hinner
      (degreeNineZeroCore_ternaryTopImage_normalGen_le
        block P hr hK N))

/-- Complete zero-core ternary row.  The inner term is supplied by the
actual induced translation module, while the outer term is the literal
ternary section of the block top. -/
theorem degreeNineZeroCore_ternary_normalGen_le
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 9)
    (i₀ : block.Points)
    (hK : degreeNineLinearBlockKernel block P = ⊥)
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    MarkedC4.normalGen (degreeNineTernarySoclePart N) ≤
      Nat.card block.Points + Nat.card block.Points / 3 := by
  apply degreeNineZeroCore_ternary_normalGen_le_of_inner block P hr hK N
  exact degreeNineTranslationCarried_normalGen_le block P hTraceyHalf
    hTraceyPerm hr i₀ N
      (degreeNineTernarySoclePart N ⊓
        degreeNineTranslationImage block P N) inf_le_right

/-! ## Prime-type sharing and the complete zero-core reduction -/

/-- The ternary/nonternary split used by the degree-nine file is exactly
the generic prime-primary split.  Hence its no-common-normal-quotient
condition is a theorem, not an additional structural input. -/
theorem degreeNine_noCommonNormalQuotient_ternary_nonTernary
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    NoCommonNormalQuotient
      (degreeNineTernarySoclePart N)
      (degreeNineNonTernarySoclePart N) := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact noCommonNormalQuotient_primePrimarySocleParts 3
    (preE7NonPairAction w U ⧸ N.1)

/-- The complementary nonternary socle part is exactly the join of its
nonabelian and abelian ambient minimal-normal factors. -/
theorem degreeNineNonTernarySoclePart_eq_sup_commutativityTypes
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    degreeNineNonTernarySoclePart N =
      degreeNineNonTernaryNonabelianSoclePart N ⊔
        degreeNineNonTernaryAbelianSoclePart N := by
  apply le_antisymm
  · apply minimalNormalSoclePart_le_of
    intro M hM hMnon3
    by_cases hcomm : IsMulCommutative M
    · exact (minimalNormal_le_minimalNormalSoclePart
          (fun K => ¬ IsPGroup 3 K ∧ IsMulCommutative K)
          M hM ⟨hMnon3, hcomm⟩).trans le_sup_right
    · exact (minimalNormal_le_minimalNormalSoclePart
          (fun K => ¬ IsPGroup 3 K ∧ ¬ IsMulCommutative K)
          M hM ⟨hMnon3, hcomm⟩).trans le_sup_left
  · apply sup_le
    · apply minimalNormalSoclePart_le_of
      intro M hM hMtype
      exact minimalNormal_le_minimalNormalSoclePart
        (fun K => ¬ IsPGroup 3 K) M hM hMtype.1
    · apply minimalNormalSoclePart_le_of
      intro M hM hMtype
      exact minimalNormal_le_minimalNormalSoclePart
        (fun K => ¬ IsPGroup 3 K) M hM hMtype.1

/-- Complete complementary row in the zero-core branch.  All nonabelian
types and all abelian nonternary prime types are aggregated before the
generator estimate, then share the same `s` slots by the perfect/abelian
Goursat theorem. -/
theorem degreeNineZeroCore_nonTernary_normalGen_le
    (hgen : PermutationSubgroupGeneratorBound)
    (hs : 2 ≤ Nat.card block.Points)
    (hr : Nat.card block.Fibre = 9)
    (hK : degreeNineLinearBlockKernel block P = ⊥)
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    MarkedC4.normalGen (degreeNineNonTernarySoclePart N) ≤
      Nat.card block.Points := by
  rw [degreeNineNonTernarySoclePart_eq_sup_commutativityTypes N]
  refine (normalGen_sup_le_max_of_noCommonNormalQuotient
    (degreeNineNonTernaryNonabelianSoclePart N)
    (degreeNineNonTernaryAbelianSoclePart N) ?_).trans ?_
  · exact noCommonNormalQuotient_nonabelian_commutativeSocleParts
      (preE7NonPairAction w U ⧸ N.1)
      (fun M => ¬ IsPGroup 3 M)
  · apply max_le
    · exact degreeNineZeroCore_nonTernaryNonabelian_normalGen_le
        block P hgen hs hr hK N
    · exact degreeNineZeroCore_nonTernaryAbelian_normalGen_le
        block P hgen hs hr hK N

/-- Once the complementary nonternary sum is carried by the literal block
top, the already-proved ternary filtration and generic prime-type sharing
give the complete `s + floor(s/3)` tuple. -/
theorem degreeNineZeroCore_socleGenerators_of_nonTernary
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 9)
    (i₀ : block.Points)
    (hK : degreeNineLinearBlockKernel block P = ⊥)
    (N : LiteralNormalAxis (preE7NonPairAction w U))
    (hnonTernary : MarkedC4.normalGen
      (degreeNineNonTernarySoclePart N) ≤
        Nat.card block.Points) :
    SocleNormalGeneratorBound
      (preE7NonPairAction w U ⧸ N.1)
      (Nat.card block.Points + Nat.card block.Points / 3) :=
  degreeNineZeroCore_socleGenerators_of_typeSharing block N
    (degreeNine_noCommonNormalQuotient_ternary_nonTernary N)
    (degreeNineZeroCore_ternary_normalGen_le block P hTraceyHalf
      hTraceyPerm hr i₀ hK N)
    hnonTernary

/-- Closed zero-core degree-nine whole-socle generator row. -/
theorem degreeNineZeroWholeCore_socleGenerators
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hgen : PermutationSubgroupGeneratorBound)
    (hs : 2 ≤ Nat.card block.Points)
    (hr : Nat.card block.Fibre = 9)
    (i₀ : block.Points)
    (hK : degreeNineLinearBlockKernel block P = ⊥)
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    SocleNormalGeneratorBound
      (preE7NonPairAction w U ⧸ N.1)
      (Nat.card block.Points + Nat.card block.Points / 3) :=
  degreeNineZeroCore_socleGenerators_of_nonTernary block P
    hTraceyHalf hTraceyPerm hr i₀ hK N
    (degreeNineZeroCore_nonTernary_normalGen_le
      block P hgen hs hr hK N)

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
