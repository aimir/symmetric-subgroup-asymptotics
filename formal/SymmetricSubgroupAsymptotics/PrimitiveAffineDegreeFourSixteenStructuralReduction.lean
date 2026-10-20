import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourInnerNonzeroSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourTwoBlockPrimitiveSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourPairCanonicalSource
import SymmetricSubgroupAsymptotics.PrimitiveFourPointAffineChoice
import SymmetricSubgroupAsymptotics.SixteenPointPairFirstGeometry

/-! Exhaust the actual sixteen-point quotient top before selecting finite
frame data. Trivial pair kernels, primitive eight-point components, and
nonzero inner ternary cores produce bounds internally. The remaining
constructors retain exactly the nontrivial pair kernel with an eligible
literal match, the primitive sixteen-point action, or the zero-ternary
four-by-four original geometry. No finite coverage is asserted here. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

private theorem eightInner_head_le_four_at
    {p : ℕ} [Fact p.Prime] {X : Type} [Finite X]
    {S : Subgroup (Equiv.Perm X)} (C : SixteenPointNonPairOriginalChart S)
    {b : Fin 16}
    (inner : OriginalMinimalBlock (A := preE7NonPairAction 16 C.index) b)
    (hp : p = 2) (hpoints : Nat.card inner.Points = 2)
    {L V : Type} [Group L] [Finite L] [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V]
    (x : X) (f : MulAction.stabilizer S x →* L) (hf : Function.Surjective f)
    (rho : Representation (ZMod p) L V) (hL : Nat.card L = 3 ∨ Nat.card L = 6)
    (hdim : Module.finrank (ZMod p) V = 2) (hrho : Function.Injective rho)
    (B : Subrepresentation
      (Representation.coind (MulAction.stabilizer S x).subtype (rho.comp f))) :
    Module.finrank (ZMod p)
      (B.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod p) S (ZMod p))) ≤ 4 := by
  subst p
  apply C.uniform_head_le x f rho 4 _ B
  intro A
  exact inner.twoBlock_head_le_four_at rfl hpoints (by simp)
    (C.points x) (C.localMap x f) (C.localMap_surjective x f hf)
    rho hL hdim hrho A

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]

local instance sixteenReduction_prime : Fact P.p.Prime := (chart block P).primeFact
local instance sixteenReduction_transitive :
    MulAction.IsPretransitive block.Top block.Points := block.top_pretransitive

/-- The eight-point-component bound through an exact original nonpair
chart, with the same external local target and original normal axes. -/
def degreeFourZeroCoreSixteenEightInnerBounds
    (published : DegreeEightCanonicalCatalogue.PublishedClassification)
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥)
    (C : SixteenPointNonPairOriginalChart block.Top) {b : Fin 16}
    (inner : OriginalMinimalBlock (A := preE7NonPairAction 16 C.index) b)
    (hinner : Nat.card inner.Fibre = 8) (hpoints : Nat.card inner.Points = 2) :
    DegreeFourZeroCoreFiniteFrameBounds block P 10 := by
  let i : block.Points := C.points.symm 0
  apply DegreeFourZeroCoreFiniteFrameBounds.ofTopCoinduced block P hr hD i
    3 4 10 (by decide)
  · intro N _
    apply C.relative_head_le 2 3 _ N
    intro M _
    exact inner.twoBlock_relativeHead_le hpoints
      (inner.eightPoint_component_normal_singletons published hinner) M
  · intro B
    exact eightInner_head_le_four_at C inner
      (degreeFour_profilePrime_eq_two block P hr) hpoints i
      (degreeFourZeroCoreTopStabilizerLocalMap block P hr hD i)
      (degreeFourZeroCoreTopStabilizerLocalMap_surjective block P hr hD i)
      (binaryAffineLocalLinearRepresentation block P).ρ
      (degreeFourZeroCoreTopStabilizerLocalTarget_card block P hr)
      (by
        change (chart block P).d = 2
        exact (degreeFour_translationDimension block P hr).2)
      (binaryAffineLocalLinearRepresentation_injective block P) B

/-- The unsolved constructors store actual finite geometry, rather than a
new hypothesis claiming the desired whole source theorem. -/
inductive DegreeFourSixteenFrameReduction : Type 1 where
  | bounded (bound : DegreeFourZeroCoreFiniteFrameBounds block P 10)
  | pair (frame : BinaryPairFrame block.Top (Fin 8))
      (nontrivialKernel : frame.top.ker ≠ ⊥)
      (literal : DegreeEightCanonicalCatalogue.TransitiveLiteralMatch frame.top.range)
      (eligible : ¬ DegreeFourEightTopEligibility.Excluded literal.index)
  | primitive (chart : SixteenPointNonPairOriginalChart block.Top)
      (primitive : MulAction.IsPreprimitive (preE7NonPairAction 16 chart.index) (Fin 16))
  | zero (chart : SixteenPointNonPairOriginalChart block.Top) (b : Fin 16)
      (inner : OriginalMinimalBlock (A := preE7NonPairAction 16 chart.index) b)
      [Nontrivial inner.Fibre]
      (profile : PrimitiveAffineProfile inner.Component inner.Fibre)
      (fibre : Nat.card inner.Fibre = 4) (points : Nat.card inner.Points = 4)
      (zeroCore : degreeFourTernaryCore inner profile = ⊥)

/-- Exhaustive original-action reduction. All classification uses are
the fixed canonical eight-point catalogue and the existing published
primitive socle dichotomy; all other alternatives are proved geometrically. -/
def degreeFourSixteenFrameReduction
    (published : DegreeEightCanonicalCatalogue.PublishedClassification)
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (hTracey : TraceySolubleOrbitInducedModuleInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥)
    (hs : Nat.card block.Points = 16) : DegreeFourSixteenFrameReduction block P := by
  by_cases hpair : Nonempty (BinaryPairFrame block.Top (Fin 8))
  · let F := Classical.choice hpair
    by_cases hker : F.top.ker = ⊥
    · exact .bounded (degreeFourZeroCoreSixteenPairTrivialBounds_of_canonical block P
        published hr hD F hker (by simp) (F.frame (0, 0)))
    · let M := degreeFourPairTopMatch block P published hr hD F (by simp)
      exact .pair F hker M (degreeFourPairTopMatch_not_excluded block P hr hD F hker M)
  · let C := sixteenPointNonPairOriginalChart block.Top hs hpair
    have hnone : ¬Nonempty (BinaryPairFrame (preE7NonPairAction 16 C.index) (Fin 8)) := by
      rintro ⟨F⟩
      have hback : relabelSubgroup C.points.symm (preE7NonPairAction 16 C.index) =
          block.Top := by
        rw [← C.matched]
        exact relabelSubgroup_symm C.points block.Top
      exact hpair ⟨hback ▸ F.relabelPoints C.points.symm⟩
    cases sixteenPointPairFirstGeometry (preE7NonPairAction 16 C.index) (by simp) with
    | pair F => exact False.elim (hnone ⟨F⟩)
    | primitive _ hp => exact .primitive C hp
    | four _ b inner hinner hpoints =>
        letI : Nontrivial inner.Fibre :=
          Finite.one_lt_card_iff_nontrivial.mp (by omega)
        let R := primitiveFourPointAffineProfile socle C.index (by decide) b inner hinner
        by_cases hzero : degreeFourTernaryCore inner R = ⊥
        · exact .zero C b inner R hinner hpoints hzero
        · exact .bounded (degreeFourZeroCoreSixteenNonzeroInnerBounds block P
            hTracey hMN hClifford hTraceyPerm hr hD C inner R hinner hpoints hzero)
    | eight _ b inner hinner hpoints =>
        exact .bounded (degreeFourZeroCoreSixteenEightInnerBounds block P
          published hr hD C inner hinner hpoints)

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
