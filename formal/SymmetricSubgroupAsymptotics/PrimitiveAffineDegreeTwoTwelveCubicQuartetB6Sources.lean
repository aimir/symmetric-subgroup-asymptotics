import SymmetricSubgroupAsymptotics.CubicRegularLiteralB6Sources
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveCubicQuartetSocles
import SymmetricSubgroupAsymptotics.BinaryPairFrameGenerators
import Mathlib.GroupTheory.GroupAction.Transitive

/-! Six existing literal cubic quartet actions receive all-normal B6
sources through the tested actual regular-two-module route. Frozen point
charts and lift bindings are reused; only small point words/pair images
and actual kernel words are checked here. -/
set_option autoImplicit false
set_option maxRecDepth 10000
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveCubicQuartetB6Sources
open BinaryThreeQuartetCubicImageSocles
open LinearSemidirectCoprimeSocleBounds LinearSemidirectSubgroupKernelChart
open PrimitiveAffineDegreeTwoTwelveCubicQuartetSocles
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

namespace Row6
abbrev Original := Row6Top
abbrev lifted := row6Lifts
abbrev K := CubicRegularLiteralB6Sources.K lifted

theorem projection_surjective : Function.Surjective (projection linear K) :=
  CubicRegularLiteralB6Sources.projection_surjective (lifted := lifted) 0 rfl

theorem scalar_nonzero : ∃ j : Fin 2, ∃ p : (projection linear K).ker,
    CubicElementaryKernelCoordinates.scalar (projection linear K)
      (CubicRegularSubgroupKernelCoordinates.moduleRep K projection_surjective).ρ
      (CubicRegularSubgroupKernelCoordinates.originalKernelChart K projection_surjective).equiv.symm
      (CubicRegularSubgroupKernelCoordinates.coordinates K projection_surjective) j p ≠ 1 := by
  refine ⟨0,⟨closureGenerators lifted 0 * closureGenerators lifted 1 * (closureGenerators lifted 0)⁻¹ * (closureGenerators lifted 1)⁻¹,?_⟩,?_⟩
  · change (lifted 0 * lifted 1 * (lifted 0)⁻¹ * (lifted 1)⁻¹).right = 1
    decide +kernel
  · change Multiplicative.ofAdd
      (CubicRegularBinaryCoordinates.scalar 0 ((lifted 0 * lifted 1 * (lifted 0)⁻¹ * (lifted 1)⁻¹).left.toAdd)) ≠ 1
    decide +kernel

def pairPoints : Fin 6 × ZMod 2 ≃ Fin 12 where
  toFun p := row6PointChart
    ((fun i : Fin 2 => if i=0 then p.2 else ((p.1.val / 3 : ℕ) : ZMod 2)),
      Multiplicative.ofAdd ((p.1.val % 3 : ℕ) : ZMod 3))
  invFun x :=
    let y := row6PointChart.symm x
    (⟨3*(y.1 1).val + (Multiplicative.toAdd y.2).val,by
      have hb := ZMod.val_lt (y.1 1)
      have hc := ZMod.val_lt (Multiplicative.toAdd y.2)
      omega⟩,y.1 0)
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def pairTop0 : Equiv.Perm (Fin 6) where
  toFun x := (#[1, 2, 0, 4, 5, 3] : Array (Fin 6))[x.val]!
  invFun x := (#[2, 0, 1, 5, 3, 4] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def pairTop1 : Equiv.Perm (Fin 6) where
  toFun x := (#[5, 3, 1, 2, 0, 4] : Array (Fin 6))[x.val]!
  invFun x := (#[4, 2, 3, 1, 5, 0] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def pairTop2 : Equiv.Perm (Fin 6) where
  toFun x := (#[3, 4, 5, 0, 1, 2] : Array (Fin 6))[x.val]!
  invFun x := (#[3, 4, 5, 0, 1, 2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pairTops : Fin 3 → Equiv.Perm (Fin 6) :=
  ![pairTop0,pairTop1,pairTop2]
private theorem pair_binding : ∀ j,
    BinaryPairFrame.Preserves pairPoints (row6Generators j) (pairTops j) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

def pairFrame : BinaryPairFrame Original (Fin 6) :=
  BinaryPairFrame.ofGenerators pairPoints row6Generators pairTops pair_binding

def ambient (j : Fin 3) : Original :=
  ⟨row6Generators j,Subgroup.subset_closure (Set.mem_range_self j)⟩
private def pointWords (x : Fin 12) : List (Fin 3) :=
  (#[[], [2,1], [1,0,0], [2,0,1], [0,0], [2,0], [2], [2,0,0], [0], [0,1], [1], [0,0,1]] : Array (List (Fin 3)))[x.val]!
private theorem pointWords_checked : ∀ x : Fin 12,
    ((pointWords x).map row6Generators).prod (0 : Fin 12) = x := by decide +kernel

theorem transitive : MulAction.IsPretransitive Original (Fin 12) := by
  apply (MulAction.isPretransitive_iff_base (G := Original) (0 : Fin 12)).mpr
  intro x
  refine ⟨((pointWords x).map ambient).prod,?_⟩
  change (((pointWords x).map ambient).prod : Equiv.Perm (Fin 12)) 0 = x
  simpa [Subgroup.val_list_prod,ambient] using pointWords_checked x

def actionCertificate (hKP : KovacsPraegerAbelianizationBound) : PreE7B6ActionCertificate Original :=
  CubicRegularLiteralB6Sources.actionCertificate
    (e := row6PointChart) (lifted := lifted) (target := row6Generators)
    (binding := row6_bindings) (hs := projection_surjective) (hscalar := scalar_nonzero)
    pairFrame hKP

theorem exists_source (hKP : KovacsPraegerAbelianizationBound) :
    ∃ p : PreE7PairActionClass 6, ∃ c : Equiv.Perm (Fin 12),
      relabelSubgroup c Original = preE7PairAction 6 p ∧
      Nonempty (PreE7B6SourceData 12 (preE7SixPairNonPairAction p)) :=
  CubicRegularLiteralB6Sources.exists_actualSource
    (e := row6PointChart) (lifted := lifted) (target := row6Generators)
    (binding := row6_bindings) (hs := projection_surjective) (hscalar := scalar_nonzero)
    transitive pairFrame hKP

def representative (hKP : KovacsPraegerAbelianizationBound) : PreE7PairActionClass 6 :=
  Classical.choose (exists_source hKP)

def source (hKP : KovacsPraegerAbelianizationBound) :
    PreE7B6SourceData 12 (preE7SixPairNonPairAction (representative hKP)) :=
  Classical.choice (Classical.choose_spec (Classical.choose_spec (exists_source hKP))).2

end Row6

namespace Row7
abbrev Original := Row7Top
abbrev lifted := row7Lifts
abbrev K := CubicRegularLiteralB6Sources.K lifted

theorem projection_surjective : Function.Surjective (projection linear K) :=
  CubicRegularLiteralB6Sources.projection_surjective (lifted := lifted) 1 rfl

theorem scalar_nonzero : ∃ j : Fin 2, ∃ p : (projection linear K).ker,
    CubicElementaryKernelCoordinates.scalar (projection linear K)
      (CubicRegularSubgroupKernelCoordinates.moduleRep K projection_surjective).ρ
      (CubicRegularSubgroupKernelCoordinates.originalKernelChart K projection_surjective).equiv.symm
      (CubicRegularSubgroupKernelCoordinates.coordinates K projection_surjective) j p ≠ 1 := by
  refine ⟨1,⟨closureGenerators lifted 0,?_⟩,?_⟩
  · change (lifted 0).right = 1
    decide +kernel
  · change Multiplicative.ofAdd
      (CubicRegularBinaryCoordinates.scalar 1 ((lifted 0).left.toAdd)) ≠ 1
    decide +kernel

def pairPoints : Fin 6 × ZMod 2 ≃ Fin 12 where
  toFun p := row7PointChart
    ((fun i : Fin 2 => if i=0 then p.2 else ((p.1.val / 3 : ℕ) : ZMod 2)),
      Multiplicative.ofAdd ((p.1.val % 3 : ℕ) : ZMod 3))
  invFun x :=
    let y := row7PointChart.symm x
    (⟨3*(y.1 1).val + (Multiplicative.toAdd y.2).val,by
      have hb := ZMod.val_lt (y.1 1)
      have hc := ZMod.val_lt (Multiplicative.toAdd y.2)
      omega⟩,y.1 0)
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def pairTop0 : Equiv.Perm (Fin 6) where
  toFun x := (#[0, 4, 5, 3, 1, 2] : Array (Fin 6))[x.val]!
  invFun x := (#[0, 4, 5, 3, 1, 2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def pairTop1 : Equiv.Perm (Fin 6) where
  toFun x := (#[4, 5, 0, 1, 2, 3] : Array (Fin 6))[x.val]!
  invFun x := (#[2, 3, 4, 5, 0, 1] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def pairTop2 : Equiv.Perm (Fin 6) where
  toFun x := (#[3, 4, 5, 0, 1, 2] : Array (Fin 6))[x.val]!
  invFun x := (#[3, 4, 5, 0, 1, 2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pairTops : Fin 3 → Equiv.Perm (Fin 6) :=
  ![pairTop0,pairTop1,pairTop2]
private theorem pair_binding : ∀ j,
    BinaryPairFrame.Preserves pairPoints (row7Generators j) (pairTops j) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

def pairFrame : BinaryPairFrame Original (Fin 6) :=
  BinaryPairFrame.ofGenerators pairPoints row7Generators pairTops pair_binding

def ambient (j : Fin 3) : Original :=
  ⟨row7Generators j,Subgroup.subset_closure (Set.mem_range_self j)⟩
private def pointWords (x : Fin 12) : List (Fin 3) :=
  (#[[], [2,1,0,1], [1,0,1], [2,1], [1], [2,1,1,0,1], [1,1,0,1], [2,1,1], [1,1], [2,0,1], [0,1], [2]] : Array (List (Fin 3)))[x.val]!
private theorem pointWords_checked : ∀ x : Fin 12,
    ((pointWords x).map row7Generators).prod (0 : Fin 12) = x := by decide +kernel

theorem transitive : MulAction.IsPretransitive Original (Fin 12) := by
  apply (MulAction.isPretransitive_iff_base (G := Original) (0 : Fin 12)).mpr
  intro x
  refine ⟨((pointWords x).map ambient).prod,?_⟩
  change (((pointWords x).map ambient).prod : Equiv.Perm (Fin 12)) 0 = x
  simpa [Subgroup.val_list_prod,ambient] using pointWords_checked x

def actionCertificate (hKP : KovacsPraegerAbelianizationBound) : PreE7B6ActionCertificate Original :=
  CubicRegularLiteralB6Sources.actionCertificate
    (e := row7PointChart) (lifted := lifted) (target := row7Generators)
    (binding := row7_bindings) (hs := projection_surjective) (hscalar := scalar_nonzero)
    pairFrame hKP

theorem exists_source (hKP : KovacsPraegerAbelianizationBound) :
    ∃ p : PreE7PairActionClass 6, ∃ c : Equiv.Perm (Fin 12),
      relabelSubgroup c Original = preE7PairAction 6 p ∧
      Nonempty (PreE7B6SourceData 12 (preE7SixPairNonPairAction p)) :=
  CubicRegularLiteralB6Sources.exists_actualSource
    (e := row7PointChart) (lifted := lifted) (target := row7Generators)
    (binding := row7_bindings) (hs := projection_surjective) (hscalar := scalar_nonzero)
    transitive pairFrame hKP

def representative (hKP : KovacsPraegerAbelianizationBound) : PreE7PairActionClass 6 :=
  Classical.choose (exists_source hKP)

def source (hKP : KovacsPraegerAbelianizationBound) :
    PreE7B6SourceData 12 (preE7SixPairNonPairAction (representative hKP)) :=
  Classical.choice (Classical.choose_spec (Classical.choose_spec (exists_source hKP))).2

end Row7

namespace Row25
abbrev Original := Row25Top
abbrev lifted := row25Lifts
abbrev K := CubicRegularLiteralB6Sources.K lifted

theorem projection_surjective : Function.Surjective (projection linear K) :=
  CubicRegularLiteralB6Sources.projection_surjective (lifted := lifted) 1 rfl

theorem scalar_nonzero : ∃ j : Fin 2, ∃ p : (projection linear K).ker,
    CubicElementaryKernelCoordinates.scalar (projection linear K)
      (CubicRegularSubgroupKernelCoordinates.moduleRep K projection_surjective).ρ
      (CubicRegularSubgroupKernelCoordinates.originalKernelChart K projection_surjective).equiv.symm
      (CubicRegularSubgroupKernelCoordinates.coordinates K projection_surjective) j p ≠ 1 := by
  refine ⟨1,⟨closureGenerators lifted 0,?_⟩,?_⟩
  · change (lifted 0).right = 1
    decide +kernel
  · change Multiplicative.ofAdd
      (CubicRegularBinaryCoordinates.scalar 1 ((lifted 0).left.toAdd)) ≠ 1
    decide +kernel

def pairPoints : Fin 6 × ZMod 2 ≃ Fin 12 where
  toFun p := row25PointChart
    ((fun i : Fin 2 => if i=0 then p.2 else ((p.1.val / 3 : ℕ) : ZMod 2)),
      Multiplicative.ofAdd ((p.1.val % 3 : ℕ) : ZMod 3))
  invFun x :=
    let y := row25PointChart.symm x
    (⟨3*(y.1 1).val + (Multiplicative.toAdd y.2).val,by
      have hb := ZMod.val_lt (y.1 1)
      have hc := ZMod.val_lt (Multiplicative.toAdd y.2)
      omega⟩,y.1 0)
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def pairTop0 : Equiv.Perm (Fin 6) where
  toFun x := (#[3, 1, 2, 0, 4, 5] : Array (Fin 6))[x.val]!
  invFun x := (#[3, 1, 2, 0, 4, 5] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def pairTop1 : Equiv.Perm (Fin 6) where
  toFun x := (#[4, 5, 0, 1, 2, 3] : Array (Fin 6))[x.val]!
  invFun x := (#[2, 3, 4, 5, 0, 1] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def pairTop2 : Equiv.Perm (Fin 6) where
  toFun x := (#[3, 4, 5, 0, 1, 2] : Array (Fin 6))[x.val]!
  invFun x := (#[3, 4, 5, 0, 1, 2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pairTops : Fin 3 → Equiv.Perm (Fin 6) :=
  ![pairTop0,pairTop1,pairTop2]
private theorem pair_binding : ∀ j,
    BinaryPairFrame.Preserves pairPoints (row25Generators j) (pairTops j) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

def pairFrame : BinaryPairFrame Original (Fin 6) :=
  BinaryPairFrame.ofGenerators pairPoints row25Generators pairTops pair_binding

def ambient (j : Fin 3) : Original :=
  ⟨row25Generators j,Subgroup.subset_closure (Set.mem_range_self j)⟩
private def pointWords (x : Fin 12) : List (Fin 3) :=
  (#[[], [2,1,1,0], [1,1,0], [2,1], [1], [2,0], [0], [2,1,1], [1,1], [2,1,0], [1,0], [2]] : Array (List (Fin 3)))[x.val]!
private theorem pointWords_checked : ∀ x : Fin 12,
    ((pointWords x).map row25Generators).prod (0 : Fin 12) = x := by decide +kernel

theorem transitive : MulAction.IsPretransitive Original (Fin 12) := by
  apply (MulAction.isPretransitive_iff_base (G := Original) (0 : Fin 12)).mpr
  intro x
  refine ⟨((pointWords x).map ambient).prod,?_⟩
  change (((pointWords x).map ambient).prod : Equiv.Perm (Fin 12)) 0 = x
  simpa [Subgroup.val_list_prod,ambient] using pointWords_checked x

def actionCertificate (hKP : KovacsPraegerAbelianizationBound) : PreE7B6ActionCertificate Original :=
  CubicRegularLiteralB6Sources.actionCertificate
    (e := row25PointChart) (lifted := lifted) (target := row25Generators)
    (binding := row25_bindings) (hs := projection_surjective) (hscalar := scalar_nonzero)
    pairFrame hKP

theorem exists_source (hKP : KovacsPraegerAbelianizationBound) :
    ∃ p : PreE7PairActionClass 6, ∃ c : Equiv.Perm (Fin 12),
      relabelSubgroup c Original = preE7PairAction 6 p ∧
      Nonempty (PreE7B6SourceData 12 (preE7SixPairNonPairAction p)) :=
  CubicRegularLiteralB6Sources.exists_actualSource
    (e := row25PointChart) (lifted := lifted) (target := row25Generators)
    (binding := row25_bindings) (hs := projection_surjective) (hscalar := scalar_nonzero)
    transitive pairFrame hKP

def representative (hKP : KovacsPraegerAbelianizationBound) : PreE7PairActionClass 6 :=
  Classical.choose (exists_source hKP)

def source (hKP : KovacsPraegerAbelianizationBound) :
    PreE7B6SourceData 12 (preE7SixPairNonPairAction (representative hKP)) :=
  Classical.choice (Classical.choose_spec (Classical.choose_spec (exists_source hKP))).2

end Row25

namespace Row26
abbrev Original := Row26Top
abbrev lifted := row26Lifts
abbrev K := CubicRegularLiteralB6Sources.K lifted

theorem projection_surjective : Function.Surjective (projection linear K) :=
  CubicRegularLiteralB6Sources.projection_surjective (lifted := lifted) 0 rfl

theorem scalar_nonzero : ∃ j : Fin 2, ∃ p : (projection linear K).ker,
    CubicElementaryKernelCoordinates.scalar (projection linear K)
      (CubicRegularSubgroupKernelCoordinates.moduleRep K projection_surjective).ρ
      (CubicRegularSubgroupKernelCoordinates.originalKernelChart K projection_surjective).equiv.symm
      (CubicRegularSubgroupKernelCoordinates.coordinates K projection_surjective) j p ≠ 1 := by
  refine ⟨0,⟨closureGenerators lifted 0 * closureGenerators lifted 1 * (closureGenerators lifted 0)⁻¹ * (closureGenerators lifted 1)⁻¹,?_⟩,?_⟩
  · change (lifted 0 * lifted 1 * (lifted 0)⁻¹ * (lifted 1)⁻¹).right = 1
    decide +kernel
  · change Multiplicative.ofAdd
      (CubicRegularBinaryCoordinates.scalar 0 ((lifted 0 * lifted 1 * (lifted 0)⁻¹ * (lifted 1)⁻¹).left.toAdd)) ≠ 1
    decide +kernel

def pairPoints : Fin 6 × ZMod 2 ≃ Fin 12 where
  toFun p := row26PointChart
    ((fun i : Fin 2 => if i=0 then p.2 else ((p.1.val / 3 : ℕ) : ZMod 2)),
      Multiplicative.ofAdd ((p.1.val % 3 : ℕ) : ZMod 3))
  invFun x :=
    let y := row26PointChart.symm x
    (⟨3*(y.1 1).val + (Multiplicative.toAdd y.2).val,by
      have hb := ZMod.val_lt (y.1 1)
      have hc := ZMod.val_lt (Multiplicative.toAdd y.2)
      omega⟩,y.1 0)
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def pairTop0 : Equiv.Perm (Fin 6) where
  toFun x := (#[1, 2, 0, 4, 5, 3] : Array (Fin 6))[x.val]!
  invFun x := (#[2, 0, 1, 5, 3, 4] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def pairTop1 : Equiv.Perm (Fin 6) where
  toFun x := (#[5, 3, 1, 2, 0, 4] : Array (Fin 6))[x.val]!
  invFun x := (#[4, 2, 3, 1, 5, 0] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def pairTop2 : Equiv.Perm (Fin 6) where
  toFun x := (#[3, 4, 5, 0, 1, 2] : Array (Fin 6))[x.val]!
  invFun x := (#[3, 4, 5, 0, 1, 2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def pairTop3 : Equiv.Perm (Fin 6) where
  toFun x := (#[0, 1, 2, 3, 4, 5] : Array (Fin 6))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pairTops : Fin 4 → Equiv.Perm (Fin 6) :=
  ![pairTop0,pairTop1,pairTop2,pairTop3]
private theorem pair_binding : ∀ j,
    BinaryPairFrame.Preserves pairPoints (row26Generators j) (pairTops j) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

def pairFrame : BinaryPairFrame Original (Fin 6) :=
  BinaryPairFrame.ofGenerators pairPoints row26Generators pairTops pair_binding

def ambient (j : Fin 4) : Original :=
  ⟨row26Generators j,Subgroup.subset_closure (Set.mem_range_self j)⟩
private def pointWords (x : Fin 12) : List (Fin 4) :=
  (#[[], [2,1], [3,0], [3], [0,0], [2,0], [2], [3,1], [0], [0,1], [1], [3,2,0]] : Array (List (Fin 4)))[x.val]!
private theorem pointWords_checked : ∀ x : Fin 12,
    ((pointWords x).map row26Generators).prod (0 : Fin 12) = x := by decide +kernel

theorem transitive : MulAction.IsPretransitive Original (Fin 12) := by
  apply (MulAction.isPretransitive_iff_base (G := Original) (0 : Fin 12)).mpr
  intro x
  refine ⟨((pointWords x).map ambient).prod,?_⟩
  change (((pointWords x).map ambient).prod : Equiv.Perm (Fin 12)) 0 = x
  simpa [Subgroup.val_list_prod,ambient] using pointWords_checked x

def actionCertificate (hKP : KovacsPraegerAbelianizationBound) : PreE7B6ActionCertificate Original :=
  CubicRegularLiteralB6Sources.actionCertificate
    (e := row26PointChart) (lifted := lifted) (target := row26Generators)
    (binding := row26_bindings) (hs := projection_surjective) (hscalar := scalar_nonzero)
    pairFrame hKP

theorem exists_source (hKP : KovacsPraegerAbelianizationBound) :
    ∃ p : PreE7PairActionClass 6, ∃ c : Equiv.Perm (Fin 12),
      relabelSubgroup c Original = preE7PairAction 6 p ∧
      Nonempty (PreE7B6SourceData 12 (preE7SixPairNonPairAction p)) :=
  CubicRegularLiteralB6Sources.exists_actualSource
    (e := row26PointChart) (lifted := lifted) (target := row26Generators)
    (binding := row26_bindings) (hs := projection_surjective) (hscalar := scalar_nonzero)
    transitive pairFrame hKP

def representative (hKP : KovacsPraegerAbelianizationBound) : PreE7PairActionClass 6 :=
  Classical.choose (exists_source hKP)

def source (hKP : KovacsPraegerAbelianizationBound) :
    PreE7B6SourceData 12 (preE7SixPairNonPairAction (representative hKP)) :=
  Classical.choice (Classical.choose_spec (Classical.choose_spec (exists_source hKP))).2

end Row26

namespace Row56
abbrev Original := Row56Top
abbrev lifted := row56Lifts
abbrev K := CubicRegularLiteralB6Sources.K lifted

theorem projection_surjective : Function.Surjective (projection linear K) :=
  CubicRegularLiteralB6Sources.projection_surjective (lifted := lifted) 2 rfl

theorem scalar_nonzero : ∃ j : Fin 2, ∃ p : (projection linear K).ker,
    CubicElementaryKernelCoordinates.scalar (projection linear K)
      (CubicRegularSubgroupKernelCoordinates.moduleRep K projection_surjective).ρ
      (CubicRegularSubgroupKernelCoordinates.originalKernelChart K projection_surjective).equiv.symm
      (CubicRegularSubgroupKernelCoordinates.coordinates K projection_surjective) j p ≠ 1 := by
  refine ⟨1,⟨closureGenerators lifted 0,?_⟩,?_⟩
  · change (lifted 0).right = 1
    decide +kernel
  · change Multiplicative.ofAdd
      (CubicRegularBinaryCoordinates.scalar 1 ((lifted 0).left.toAdd)) ≠ 1
    decide +kernel

def pairPoints : Fin 6 × ZMod 2 ≃ Fin 12 where
  toFun p := row56PointChart
    ((fun i : Fin 2 => if i=0 then p.2 else ((p.1.val / 3 : ℕ) : ZMod 2)),
      Multiplicative.ofAdd ((p.1.val % 3 : ℕ) : ZMod 3))
  invFun x :=
    let y := row56PointChart.symm x
    (⟨3*(y.1 1).val + (Multiplicative.toAdd y.2).val,by
      have hb := ZMod.val_lt (y.1 1)
      have hc := ZMod.val_lt (Multiplicative.toAdd y.2)
      omega⟩,y.1 0)
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def pairTop0 : Equiv.Perm (Fin 6) where
  toFun x := (#[0, 1, 5, 3, 4, 2] : Array (Fin 6))[x.val]!
  invFun x := (#[0, 1, 5, 3, 4, 2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def pairTop1 : Equiv.Perm (Fin 6) where
  toFun x := (#[3, 1, 5, 0, 4, 2] : Array (Fin 6))[x.val]!
  invFun x := (#[3, 1, 5, 0, 4, 2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def pairTop2 : Equiv.Perm (Fin 6) where
  toFun x := (#[4, 2, 3, 1, 5, 0] : Array (Fin 6))[x.val]!
  invFun x := (#[5, 3, 1, 2, 0, 4] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pairTops : Fin 3 → Equiv.Perm (Fin 6) :=
  ![pairTop0,pairTop1,pairTop2]
private theorem pair_binding : ∀ j,
    BinaryPairFrame.Preserves pairPoints (row56Generators j) (pairTops j) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

def pairFrame : BinaryPairFrame Original (Fin 6) :=
  BinaryPairFrame.ofGenerators pairPoints row56Generators pairTops pair_binding

def ambient (j : Fin 3) : Original :=
  ⟨row56Generators j,Subgroup.subset_closure (Set.mem_range_self j)⟩
private def pointWords (x : Fin 12) : List (Fin 3) :=
  (#[[], [2,1], [0,2,2], [2,0,2,2,1], [2], [2,2,1], [2,0,2,2], [2,2,0,2,2,1], [2,2], [1], [2,2,0,2,2], [0,2,2,1]] : Array (List (Fin 3)))[x.val]!
private theorem pointWords_checked : ∀ x : Fin 12,
    ((pointWords x).map row56Generators).prod (0 : Fin 12) = x := by decide +kernel

theorem transitive : MulAction.IsPretransitive Original (Fin 12) := by
  apply (MulAction.isPretransitive_iff_base (G := Original) (0 : Fin 12)).mpr
  intro x
  refine ⟨((pointWords x).map ambient).prod,?_⟩
  change (((pointWords x).map ambient).prod : Equiv.Perm (Fin 12)) 0 = x
  simpa [Subgroup.val_list_prod,ambient] using pointWords_checked x

def actionCertificate (hKP : KovacsPraegerAbelianizationBound) : PreE7B6ActionCertificate Original :=
  CubicRegularLiteralB6Sources.actionCertificate
    (e := row56PointChart) (lifted := lifted) (target := row56Generators)
    (binding := row56_bindings) (hs := projection_surjective) (hscalar := scalar_nonzero)
    pairFrame hKP

theorem exists_source (hKP : KovacsPraegerAbelianizationBound) :
    ∃ p : PreE7PairActionClass 6, ∃ c : Equiv.Perm (Fin 12),
      relabelSubgroup c Original = preE7PairAction 6 p ∧
      Nonempty (PreE7B6SourceData 12 (preE7SixPairNonPairAction p)) :=
  CubicRegularLiteralB6Sources.exists_actualSource
    (e := row56PointChart) (lifted := lifted) (target := row56Generators)
    (binding := row56_bindings) (hs := projection_surjective) (hscalar := scalar_nonzero)
    transitive pairFrame hKP

def representative (hKP : KovacsPraegerAbelianizationBound) : PreE7PairActionClass 6 :=
  Classical.choose (exists_source hKP)

def source (hKP : KovacsPraegerAbelianizationBound) :
    PreE7B6SourceData 12 (preE7SixPairNonPairAction (representative hKP)) :=
  Classical.choice (Classical.choose_spec (Classical.choose_spec (exists_source hKP))).2

end Row56

namespace Row90
abbrev Original := Row90Top
abbrev lifted := row90Lifts
abbrev K := CubicRegularLiteralB6Sources.K lifted

theorem projection_surjective : Function.Surjective (projection linear K) :=
  CubicRegularLiteralB6Sources.projection_surjective (lifted := lifted) 2 rfl

theorem scalar_nonzero : ∃ j : Fin 2, ∃ p : (projection linear K).ker,
    CubicElementaryKernelCoordinates.scalar (projection linear K)
      (CubicRegularSubgroupKernelCoordinates.moduleRep K projection_surjective).ρ
      (CubicRegularSubgroupKernelCoordinates.originalKernelChart K projection_surjective).equiv.symm
      (CubicRegularSubgroupKernelCoordinates.coordinates K projection_surjective) j p ≠ 1 := by
  refine ⟨0,⟨closureGenerators lifted 0,?_⟩,?_⟩
  · change (lifted 0).right = 1
    decide +kernel
  · change Multiplicative.ofAdd
      (CubicRegularBinaryCoordinates.scalar 0 ((lifted 0).left.toAdd)) ≠ 1
    decide +kernel

def pairPoints : Fin 6 × ZMod 2 ≃ Fin 12 where
  toFun p := row90PointChart
    ((fun i : Fin 2 => if i=0 then p.2 else ((p.1.val / 3 : ℕ) : ZMod 2)),
      Multiplicative.ofAdd ((p.1.val % 3 : ℕ) : ZMod 3))
  invFun x :=
    let y := row90PointChart.symm x
    (⟨3*(y.1 1).val + (Multiplicative.toAdd y.2).val,by
      have hb := ZMod.val_lt (y.1 1)
      have hc := ZMod.val_lt (Multiplicative.toAdd y.2)
      omega⟩,y.1 0)
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def pairTop0 : Equiv.Perm (Fin 6) where
  toFun x := (#[0, 1, 5, 3, 4, 2] : Array (Fin 6))[x.val]!
  invFun x := (#[0, 1, 5, 3, 4, 2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def pairTop1 : Equiv.Perm (Fin 6) where
  toFun x := (#[0, 1, 5, 3, 4, 2] : Array (Fin 6))[x.val]!
  invFun x := (#[0, 1, 5, 3, 4, 2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def pairTop2 : Equiv.Perm (Fin 6) where
  toFun x := (#[4, 2, 3, 1, 5, 0] : Array (Fin 6))[x.val]!
  invFun x := (#[5, 3, 1, 2, 0, 4] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pairTops : Fin 3 → Equiv.Perm (Fin 6) :=
  ![pairTop0,pairTop1,pairTop2]
private theorem pair_binding : ∀ j,
    BinaryPairFrame.Preserves pairPoints (row90Generators j) (pairTops j) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

def pairFrame : BinaryPairFrame Original (Fin 6) :=
  BinaryPairFrame.ofGenerators pairPoints row90Generators pairTops pair_binding

def ambient (j : Fin 3) : Original :=
  ⟨row90Generators j,Subgroup.subset_closure (Set.mem_range_self j)⟩
private def pointWords (x : Fin 12) : List (Fin 3) :=
  (#[[], [2,2,0,2,2], [1,2,2], [2,1,0,2,2], [2], [0,2,2], [2,1,2,2], [2,2,1,0,2,2], [2,2], [2,0,2,2], [2,2,1,2,2], [1,0,2,2]] : Array (List (Fin 3)))[x.val]!
private theorem pointWords_checked : ∀ x : Fin 12,
    ((pointWords x).map row90Generators).prod (0 : Fin 12) = x := by decide +kernel

theorem transitive : MulAction.IsPretransitive Original (Fin 12) := by
  apply (MulAction.isPretransitive_iff_base (G := Original) (0 : Fin 12)).mpr
  intro x
  refine ⟨((pointWords x).map ambient).prod,?_⟩
  change (((pointWords x).map ambient).prod : Equiv.Perm (Fin 12)) 0 = x
  simpa [Subgroup.val_list_prod,ambient] using pointWords_checked x

def actionCertificate (hKP : KovacsPraegerAbelianizationBound) : PreE7B6ActionCertificate Original :=
  CubicRegularLiteralB6Sources.actionCertificate
    (e := row90PointChart) (lifted := lifted) (target := row90Generators)
    (binding := row90_bindings) (hs := projection_surjective) (hscalar := scalar_nonzero)
    pairFrame hKP

theorem exists_source (hKP : KovacsPraegerAbelianizationBound) :
    ∃ p : PreE7PairActionClass 6, ∃ c : Equiv.Perm (Fin 12),
      relabelSubgroup c Original = preE7PairAction 6 p ∧
      Nonempty (PreE7B6SourceData 12 (preE7SixPairNonPairAction p)) :=
  CubicRegularLiteralB6Sources.exists_actualSource
    (e := row90PointChart) (lifted := lifted) (target := row90Generators)
    (binding := row90_bindings) (hs := projection_surjective) (hscalar := scalar_nonzero)
    transitive pairFrame hKP

def representative (hKP : KovacsPraegerAbelianizationBound) : PreE7PairActionClass 6 :=
  Classical.choose (exists_source hKP)

def source (hKP : KovacsPraegerAbelianizationBound) :
    PreE7B6SourceData 12 (preE7SixPairNonPairAction (representative hKP)) :=
  Classical.choice (Classical.choose_spec (Classical.choose_spec (exists_source hKP))).2

end Row90
end PrimitiveAffineDegreeTwoTwelveCubicQuartetB6Sources
end SymmetricSubgroupAsymptotics
end
