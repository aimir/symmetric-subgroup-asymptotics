import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeSignedQuotientPairFrame
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeNineSocleGenerators

/-!
# Reflection of the signed block kernel in the literal pair frame

The pair frame used by the degree-two finite slices is not an auxiliary
pairing.  Its top is the actual block action of `U/E`, so its pair kernel is
exactly the already selected linear block kernel, transported through the
literal range equivalence.  The statements here let finite pair classifiers
retain the zero/nonzero kernel branch instead of forgetting it during point
relabeling.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- The top homomorphism used in the signed pair frame has the literal
linear block kernel. -/
theorem degreeThreeSignedQuotientPairTop_ker :
    (degreeThreeSignedQuotientPairTop block P).ker =
      degreeNineLinearBlockKernel block P := by
  ext q
  change
    (block.Top.subtype
      (binaryAffineQuotientTopMap block P q) = 1) ↔
      binaryAffineQuotientTopMap block P q = 1
  constructor
  · intro h
    exact Subtype.ext h
  · intro h
    rw [h, map_one]

/-- Vanishing of the pair-frame kernel would force vanishing of the actual
signed block kernel. -/
theorem degreeThreeSignedQuotientPairFrame_top_ker_ne_bot
    (hr : Nat.card block.Fibre = 3)
    (hK : degreeNineLinearBlockKernel block P ≠ ⊥) :
    (degreeThreeSignedQuotientPairFrame block P hr).top.ker ≠ ⊥ := by
  intro hzero
  have hframe : Function.Injective
      (degreeThreeSignedQuotientPairFrame block P hr).top := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact hzero
  have htop : Function.Injective
      (degreeThreeSignedQuotientPairTop block P) := by
    intro x y hxy
    apply (degreeThreeSignedQuotientRangeEquiv block P).injective
    apply hframe
    simpa only [degreeThreeSignedQuotientPairFrame,
      BinaryPairFrame.ofEquiv, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using hxy
  apply hK
  rw [← degreeThreeSignedQuotientPairTop_ker block P,
    MonoidHom.ker_eq_bot_iff]
  exact htop

end PrimitiveAffineImprimitiveBlockTransfer

namespace BinaryPairFrame

/-- Changing pair labels preserves nontriviality of the literal pair
kernel. -/
theorem reindex_top_ker_ne_bot
    {X I J : Type*} {A : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame A I) (e : I ≃ J)
    (hF : F.top.ker ≠ ⊥) : (F.reindex e).top.ker ≠ ⊥ := by
  intro hzero
  have hinj : Function.Injective (F.reindex e).top := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact hzero
  have hinjF : Function.Injective F.top := by
    intro a b hab
    apply hinj
    apply Equiv.ext
    intro j
    change e (F.top a (e.symm j)) = e (F.top b (e.symm j))
    rw [hab]
  exact hF ((MonoidHom.ker_eq_bot_iff F.top).2 hinjF)

/-- Relabelling the physical points preserves nontriviality of the literal
pair kernel. -/
theorem relabelPoints_top_ker_ne_bot
    {X Y I : Type*} {A : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame A I) (e : X ≃ Y)
    (hF : F.top.ker ≠ ⊥) : (F.relabelPoints e).top.ker ≠ ⊥ := by
  intro hzero
  have hinj : Function.Injective (F.relabelPoints e).top := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact hzero
  have hinjF : Function.Injective F.top := by
    intro a b hab
    apply (BinaryPairFrame.sourceRelabelEquiv (U := A) e).injective
    apply hinj
    apply Equiv.ext
    intro i
    rw [F.relabelPoints_top_sourceRelabelEquiv,
      F.relabelPoints_top_sourceRelabelEquiv, hab]
  exact hF ((MonoidHom.ker_eq_bot_iff F.top).2 hinjF)

end BinaryPairFrame

namespace PrimitiveAffineImprimitiveBlockTransfer

/-- The fixed-degree chart consumed by a degree-two package still remembers
that the actual signed block kernel is nonzero. -/
theorem degreeThreeSignedQuotientPairChart_frame_top_ker_ne_bot
    {w : ℕ} {U : PreE7NonPairActionClass w}
    {basePoint : Fin w}
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (hr : Nat.card block.Fibre = 3)
    {s : ℕ} (hs : Nat.card block.Points = s)
    (hcomponent : Nat.card block.Component = 6)
    (hK : degreeNineLinearBlockKernel block P ≠ ⊥) :
    (degreeThreeSignedQuotientPairChart block P hr hs hcomponent).frame.top.ker ≠
      ⊥ := by
  let e : Fin (quotientDegree block) ≃ Fin (2 * s) := finCongr (by
    rw [quotientDegree_eq block, hr, hs])
  let F0 := degreeThreeSignedQuotientPairFrame block P hr
  let F1 := F0.relabelPoints e
  let idx := Finite.equivFinOfCardEq hs
  have h0 : F0.top.ker ≠ ⊥ :=
    degreeThreeSignedQuotientPairFrame_top_ker_ne_bot block P hr hK
  have h1 : F1.top.ker ≠ ⊥ :=
    BinaryPairFrame.relabelPoints_top_ker_ne_bot F0 e h0
  have h2 : (F1.reindex idx).top.ker ≠ ⊥ :=
    BinaryPairFrame.reindex_top_ker_ne_bot F1 idx h1
  simpa only [degreeThreeSignedQuotientPairChart, e, F0, F1, idx] using h2

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
