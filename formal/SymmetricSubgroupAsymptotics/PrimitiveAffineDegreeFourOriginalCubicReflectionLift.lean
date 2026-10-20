import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourOriginalCubicBlockGauge
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourS4OriginalGroupChart
import SymmetricSubgroupAsymptotics.CubicFourPointReflectionLift

/-! The odd reflection is constructed in the literal original group,
through its actual full four-block image. No splitting is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeFourS4OriginalPointChart

local instance originalReflectionPrimeThree : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre] (C : DegreeFourS4OriginalPointChart block)

def physicalTopEquiv (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥) (d : block.Points ≃ Fin 4) :
    DegreeFourComplementQuotient block P ≃* Equiv.Perm (Fin 4) :=
  ((degreeFourZeroCoreTopEquiv block P hr hD).trans C.topEquiv).trans
    (C.points.symm.trans d).permCongrHom

theorem physicalTopEquiv_action (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥) (d : block.Points ≃ Fin 4)
    (g : preE7NonPairAction w U) (i : block.Points) :
    degreeFourPhysicalCanonicalMap block P
      (physicalTopEquiv block P C hr hD d) g (d i) = d (g • i) := by
  simp [degreeFourPhysicalCanonicalMap,physicalTopEquiv,topEquiv,
    Equiv.permCongr_apply,degreeFourZeroCoreTopEquiv_apply,
    degreeFourQuotientTopMap] <;> rfl

include C in
theorem originalCubicReflectionLift (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (S : Sylow 3 (preE7NonPairAction w U)) (s : preE7NonPairAction w U)
    (d : block.Points ≃ Fin 4)
    (hgen : (S : Subgroup (preE7NonPairAction w U)) = Subgroup.zpowers s)
    (hd : ∀ i : block.Points,
      d (s • i) = BinaryFourCubicNormalizerPointShapes.blockCycle (d i))
    (hzero : ∀ e : preE7NonPairAction w U, e ∈ E block P →
      (∀ t : preE7NonPairAction w U, t ∈ (S : Subgroup (preE7NonPairAction w U)) →
        e*t = t*e) → e = 1) :
    ∃ g : preE7NonPairAction w U,
      g ∈ Subgroup.normalizer (S : Set (preE7NonPairAction w U)) ∧
      g^2 = 1 ∧ g*s*g⁻¹ = s⁻¹ ∧
      ∀ i : block.Points, d (g • i) = Equiv.swap 2 3 (d i) := by
  let e := physicalTopEquiv block P C hr hD d
  let f := degreeFourPhysicalCanonicalMap block P e
  have hfs : f s = BinaryFourCubicNormalizerPointShapes.blockCycle := by
    apply Equiv.ext
    intro j
    obtain ⟨i,rfl⟩ := d.surjective j
    exact (physicalTopEquiv_action block P C hr hD d s i).trans (hd i)
  have hz : ∀ a, a ∈ f.ker →
      (∀ t, t ∈ (S : Subgroup (preE7NonPairAction w U)) → a*t=t*a) → a=1 := by
    intro a ha hcomm
    apply hzero a _ hcomm
    have hk := degreeFourPhysicalCanonicalMap_ker block P e
    exact hk ▸ ha
  obtain ⟨g,hgn,hfg,hg2,hgs⟩ := CubicFourPointReflectionLift.exists_lift f
    (degreeFourPhysicalCanonicalMap_surjective block P e) S s hgen hfs
    (degreeFourOriginalCubicSylow_injective block P e hr S) hz
  refine ⟨g,hgn,hg2,hgs,?_⟩
  intro i
  rw [← physicalTopEquiv_action block P C hr hD d g i]
  exact congrArg (fun p : Equiv.Perm (Fin 4) => p (d i)) hfg

end DegreeFourS4OriginalPointChart
end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
