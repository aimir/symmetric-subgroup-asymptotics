import SymmetricSubgroupAsymptotics.PrimitiveAffineZeroCoreCoinducedConsumer
import SymmetricSubgroupAsymptotics.BinaryFourCanonicalSymmetricNaturalChart

/-! The original zero-core four-block quotient and its actual inducing
stabilizer in canonical S4 coordinates. The chart records an exact point
relabeling, never an abstract group-order match or numerical bound. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]

structure DegreeFourS4OriginalPointChart where
  points : block.Points ≃ Fin 4
  matched : relabelSubgroup points block.Top = ⊤

namespace DegreeFourS4OriginalPointChart

variable (C : DegreeFourS4OriginalPointChart block)

def sourcePoint : block.Points := C.points.symm 0

def topEquiv : block.Top ≃* Equiv.Perm (Fin 4) :=
  ((C.points.permCongrHom.subgroupMap block.Top).trans
    (MulEquiv.subgroupCongr C.matched)).trans Subgroup.topEquiv

def groupEquiv (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥) :
    DegreeFourComplementQuotient block P ≃* BinaryFourSymmetricBlockActions.SymmetricComplement :=
  ((degreeFourZeroCoreTopEquiv block P hr hD).trans (C.topEquiv)).trans
    BinaryFourCanonicalSymmetricInducedChart.naturalGroupEquiv.symm

theorem groupEquiv_action (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (g : DegreeFourComplementQuotient block P) (j : block.Points) :
    C.points (binaryAffineQuotientTopMap block P g • j) =
      (groupEquiv (block := block) (P := P) (C := C) hr hD) g • C.points j := by
  rw [← BinaryFourCanonicalSymmetricInducedChart.naturalGroupEquiv_apply]
  simp [groupEquiv, topEquiv, Equiv.permCongr_apply,
    degreeFourZeroCoreTopEquiv_apply, binaryAffineQuotientTopMap, degreeFourQuotientTopMap] <;> rfl

def stabilizerEquiv (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥) :
    fullFrameInducedStabilizer block P C.sourcePoint ≃*
      BinaryFourCanonicalSymmetricInducedChart.stabilizer where
  toFun h := ⟨(groupEquiv (block := block) (P := P) (C := C) hr hD) h.1, by
    have hs : binaryAffineQuotientTopMap block P h.1 • C.points.symm 0 = C.points.symm 0 := h.2
    have he := (groupEquiv_action (block := block) (P := P) (C := C) hr hD) h.1 (C.points.symm 0)
    rw [hs, C.points.apply_symm_apply] at he
    exact he.symm⟩
  invFun h := ⟨((groupEquiv (block := block) (P := P) (C := C) hr hD)).symm h.1, by
    apply C.points.injective
    have he := (groupEquiv_action (block := block) (P := P) (C := C) hr hD)
      (((groupEquiv (block := block) (P := P) (C := C) hr hD)).symm h.1) (C.points.symm 0)
    rw [((groupEquiv (block := block) (P := P) (C := C) hr hD)).apply_symm_apply, C.points.apply_symm_apply] at he
    have hh : h.1 • (0 : Fin 4) = 0 := h.2
    rw [hh] at he
    simpa only [sourcePoint, binaryAffineQuotientTopMap, Equiv.apply_symm_apply] using he⟩
  left_inv h := Subtype.ext (((groupEquiv (block := block) (P := P) (C := C) hr hD)).symm_apply_apply h.1)
  right_inv h := Subtype.ext (((groupEquiv (block := block) (P := P) (C := C) hr hD)).apply_symm_apply h.1)
  map_mul' h k := Subtype.ext (((groupEquiv (block := block) (P := P) (C := C) hr hD)).map_mul h.1 k.1)

theorem stabilizerEquiv_commutes (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (h : fullFrameInducedStabilizer block P C.sourcePoint) :
    (groupEquiv (block := block) (P := P) (C := C) hr hD) h.1 = ((stabilizerEquiv (block := block) (P := P) (C := C) hr hD) h).1 := rfl

end DegreeFourS4OriginalPointChart
end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
