import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourPairFrameSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFramePortableTable

/-!
The nontrivial pair-kernel branch consumes an existing complete eight-point
table at its actual image and stabilizer. The two numerical premises of the
structural frame theorem are discharged here from the retained normal and
local-module certificates. The remaining correspondence is an exact ambient
and stabilizer equivalence, not an asserted head bound or an abstract group
isomorphism without the original stabilizer.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

namespace GeneratedTopTable

/-- Change the prime before introducing the dependent affine profile. -/
theorem coind_head_le_two_of_equiv_at
    (T : GeneratedTopData) (C : GeneratedTopTable T)
    {p : ℕ} [Fact p.Prime] (hp : p = 2)
    {G L V : Type} [Group G] [Finite G] [Group L] [Finite L]
    [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (H : Subgroup G) (eG : G ≃* T.ModelGroup)
    (eH : H ≃* T.sourceStabilizer)
    (commutes : ∀ h : H, eG (h : G) = (eH h : T.ModelGroup))
    (f : H →* L) (hf : Function.Surjective f)
    (hL : Nat.card L = 3 ∨ (Nat.card L = 6 ∧ ¬ IsMulCommutative L))
    (tau : Representation (ZMod p) L V)
    (htau : Function.Injective tau) (hV : Module.finrank (ZMod p) V = 2)
    (B : Subrepresentation (Representation.coind H.subtype (tau.comp f))) :
    Module.finrank (ZMod p)
      (B.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod p) G (ZMod p))) ≤ 2 := by
  subst p
  exact C.coind_head_le_two_of_equiv T H eG eH commutes f hf hL tau htau hV B

end GeneratedTopTable

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
  (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

local instance : Fact P.p.Prime := (chart block P).primeFact
local instance : MulAction.IsPretransitive block.Top block.Points := block.top_pretransitive

/-- An actual complete quotient table closes the entire nontrivial-kernel
pair branch. Every original normal quotient remains owned by the same
profile; no finite certificate enumerates or replaces that original group. -/
def degreeFourZeroCoreSixteenPairKernelBounds_of_table
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥)
    {I : Type} [Finite I] (F : BinaryPairFrame block.Top I)
    (hker : F.top.ker ≠ ⊥) (hcard : Nat.card I = 8) (i : I)
    (T : GeneratedTopData) (C : GeneratedTopTable T)
    (eG : F.top.range ≃* T.ModelGroup)
    (eH : F.pairTopStabilizer i ≃* T.sourceStabilizer)
    (commutes : ∀ h : F.pairTopStabilizer i,
      eG (h : F.top.range) = (eH h : T.ModelGroup)) :
    DegreeFourZeroCoreFiniteFrameBounds block P 10 := by
  apply degreeFourZeroCoreSixteenPairKernelNontrivialBounds
    block P hr hD F hker hcard i
  · intro N _
    exact T.topRegistry.bound_equiv eG.symm N
  · intro B
    have hdim : Module.finrank (ZMod P.p) (chart block P).V = 2 := by
      change (chart block P).d = 2
      exact (degreeFour_translationDimension block P hr).2
    exact C.coind_head_le_two_of_equiv_at T
      (degreeFour_profilePrime_eq_two block P hr)
      (F.pairTopStabilizer i) eG eH commutes
      (F.descendedPointLocalMap hker i
        (degreeFourPairPointLocalMap block P hr hD F i)
        (degreeFourZeroCoreTopStabilizerLocalMap_surjective block P hr hD (F.frame (i, 0)))
        (degreeFourLocalTarget_eligible block P hr))
      (F.descendedPointLocalMap_surjective hker i
        (degreeFourPairPointLocalMap block P hr hD F i)
        (degreeFourZeroCoreTopStabilizerLocalMap_surjective block P hr hD (F.frame (i, 0)))
        (degreeFourLocalTarget_eligible block P hr))
      (degreeFourLocalTarget_eligible block P hr)
      (binaryAffineLocalLinearRepresentation block P).ρ
      (binaryAffineLocalLinearRepresentation_injective block P) hdim B

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
