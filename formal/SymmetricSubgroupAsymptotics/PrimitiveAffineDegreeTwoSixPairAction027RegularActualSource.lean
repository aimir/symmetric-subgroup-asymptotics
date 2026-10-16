import SymmetricSubgroupAsymptotics.CubicRegularLiteralB6Sources
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction025RegularPilot
import SymmetricSubgroupAsymptotics.BinaryPairFrameGenerators
import Mathlib.GroupTheory.GroupAction.Transitive

/-! Actual selected six-block dataset action27, from its original12point
generators. Dataset SHA256 446f54807b4f31114d559c9459fb529bd0eb83bbdd744e563a799521ddaa43d3.
No Cayley/normal certificate, source-order premise or fixed-label coverage.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineDegreeTwoSixPairAction027RegularActualSource
open BinaryThreeQuartetCubicImageSocles
open LinearSemidirectCoprimeSocleBounds LinearSemidirectSubgroupKernelChart

private def generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 3, 5, 4, 6, 7, 8, 9, 11, 10] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 3, 5, 4, 6, 7, 8, 9, 11, 10] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 3, 2, 4, 5, 6, 7, 9, 8, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 3, 2, 4, 5, 6, 7, 9, 8, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[1, 0, 2, 3, 4, 5, 7, 6, 8, 9, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[1, 0, 2, 3, 4, 5, 7, 6, 8, 9, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[10, 11, 6, 7, 2, 3, 4, 5, 0, 1, 8, 9] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 4, 5, 6, 7, 2, 3, 10, 11, 0, 1] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator4 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 8, 9, 10, 11, 6, 7, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 8, 9, 10, 11, 6, 7, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator5 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 7, 2, 3, 10, 11, 0, 1, 8, 9, 4, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 7, 2, 3, 10, 11, 0, 1, 8, 9, 4, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators : Fin 6 → Equiv.Perm (Fin 12) :=
  ![generator0,generator1,generator2,generator3,generator4,generator5]
abbrev Original := Subgroup.closure (Set.range generators)
abbrev pointChart := PrimitiveAffineDegreeTwoSixPairAction025RegularPilot.pointChart

private def offset (j : Fin 6) (x : Bits) : ZMod 2 :=
  if x.1=0 then
    (![![0, 1, 0], ![0, 0, 1], ![1, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0]] : Fin 6 → Fin 3 → ZMod 2) j
      ⟨(Multiplicative.toAdd x.2).val,ZMod.val_lt _⟩
  else
    (![![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, 0], ![0, 1, 1], ![1, 1, 0]] : Fin 6 → Fin 3 → ZMod 2) j
      ⟨(Multiplicative.toAdd x.2).val,ZMod.val_lt _⟩

def lifted (j : Fin 6) : Model :=
  ⟨Multiplicative.ofAdd (offset j),Multiplicative.ofAdd ((![0, 0, 0, 1, 0, 0] : Fin 6 → ZMod 3) j)⟩

theorem binding : ∀ j, literalAction pointChart (lifted j) = generators j := by
  intro j
  apply Equiv.ext
  intro x
  revert j x
  decide +kernel

abbrev K := CubicRegularLiteralB6Sources.K lifted

theorem projection_surjective : Function.Surjective (projection linear K) :=
  CubicRegularLiteralB6Sources.projection_surjective (lifted := lifted) 3 rfl

theorem scalar_nonzero : ∃ j : Fin 2, ∃ p : (projection linear K).ker,
    CubicElementaryKernelCoordinates.scalar (projection linear K)
      (CubicRegularSubgroupKernelCoordinates.moduleRep K projection_surjective).ρ
      (CubicRegularSubgroupKernelCoordinates.originalKernelChart K projection_surjective).equiv.symm
      (CubicRegularSubgroupKernelCoordinates.coordinates K projection_surjective) j p ≠ 1 := by
  refine ⟨0,⟨closureGenerators lifted 0,by rfl⟩,?_⟩
  change Multiplicative.ofAdd
    (CubicRegularBinaryCoordinates.scalar 0 ((lifted 0).left.toAdd)) ≠ 1
  decide +kernel

def pairPoints : Fin 6 × ZMod 2 ≃ Fin 12 :=
  (Equiv.prodCongr (Equiv.refl (Fin 6)) (ZMod.finEquiv 2).symm.toEquiv).trans finProdFinEquiv

private def pairTop0 : Equiv.Perm (Fin 6) where
  toFun x := (#[0, 1, 2, 3, 4, 5] : Array (Fin 6))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def pairTop1 : Equiv.Perm (Fin 6) where
  toFun x := (#[0, 1, 2, 3, 4, 5] : Array (Fin 6))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def pairTop2 : Equiv.Perm (Fin 6) where
  toFun x := (#[0, 1, 2, 3, 4, 5] : Array (Fin 6))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def pairTop3 : Equiv.Perm (Fin 6) where
  toFun x := (#[5, 3, 1, 2, 0, 4] : Array (Fin 6))[x.val]!
  invFun x := (#[4, 2, 3, 1, 5, 0] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def pairTop4 : Equiv.Perm (Fin 6) where
  toFun x := (#[0, 4, 5, 3, 1, 2] : Array (Fin 6))[x.val]!
  invFun x := (#[0, 4, 5, 3, 1, 2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def pairTop5 : Equiv.Perm (Fin 6) where
  toFun x := (#[3, 1, 5, 0, 4, 2] : Array (Fin 6))[x.val]!
  invFun x := (#[3, 1, 5, 0, 4, 2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pairTops : Fin 6 → Equiv.Perm (Fin 6) :=
  ![pairTop0,pairTop1,pairTop2,pairTop3,pairTop4,pairTop5]
private theorem pair_binding : ∀ j,
    BinaryPairFrame.Preserves pairPoints (generators j) (pairTops j) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

def pairFrame : BinaryPairFrame Original (Fin 6) :=
  BinaryPairFrame.ofGenerators pairPoints generators pairTops pair_binding

def ambient (j : Fin 6) : Original :=
  ⟨generators j,Subgroup.subset_closure (Set.mem_range_self j)⟩
private def pointWords (x : Fin 12) : List (Fin 6) :=
  (#[[], [2], [4,3,3], [4,3,3,2], [4,3], [4,3,2], [5], [5,2], [3,3], [3,3,2], [3], [3,2]] : Array (List (Fin 6)))[x.val]!
private theorem pointWords_checked : ∀ x : Fin 12,
    ((pointWords x).map generators).prod (0 : Fin 12) = x := by decide +kernel

theorem transitive : MulAction.IsPretransitive Original (Fin 12) := by
  apply (MulAction.isPretransitive_iff_base (G := Original) (0 : Fin 12)).mpr
  intro x
  refine ⟨((pointWords x).map ambient).prod,?_⟩
  change (((pointWords x).map ambient).prod : Equiv.Perm (Fin 12)) 0 = x
  simpa [Subgroup.val_list_prod,ambient] using pointWords_checked x

def actionCertificate (hKP : KovacsPraegerAbelianizationBound) : PreE7B6ActionCertificate Original :=
  CubicRegularLiteralB6Sources.actionCertificate
    (e := pointChart) (lifted := lifted) (target := generators) (binding := binding)
    (hs := projection_surjective) (hscalar := scalar_nonzero) pairFrame hKP

theorem exists_source (hKP : KovacsPraegerAbelianizationBound) :
    ∃ p : PreE7PairActionClass 6, ∃ c : Equiv.Perm (Fin 12),
      relabelSubgroup c Original = preE7PairAction 6 p ∧
      Nonempty (PreE7B6SourceData 12 (preE7SixPairNonPairAction p)) :=
  CubicRegularLiteralB6Sources.exists_actualSource
    (e := pointChart) (lifted := lifted) (target := generators) (binding := binding)
    (hs := projection_surjective) (hscalar := scalar_nonzero) transitive pairFrame hKP

def representative (hKP : KovacsPraegerAbelianizationBound) : PreE7PairActionClass 6 :=
  Classical.choose (exists_source hKP)

def source (hKP : KovacsPraegerAbelianizationBound) :
    PreE7B6SourceData 12 (preE7SixPairNonPairAction (representative hKP)) :=
  Classical.choice (Classical.choose_spec (Classical.choose_spec (exists_source hKP))).2

theorem actual_correspondence (hKP : KovacsPraegerAbelianizationBound) :
    ∃ c : Equiv.Perm (Fin 12), relabelSubgroup c Original =
      preE7PairAction 6 (representative hKP) := by
  have h := Classical.choose_spec (exists_source hKP)
  exact ⟨Classical.choose h,(Classical.choose_spec h).1⟩

end PrimitiveAffineDegreeTwoSixPairAction027RegularActualSource
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics
end
