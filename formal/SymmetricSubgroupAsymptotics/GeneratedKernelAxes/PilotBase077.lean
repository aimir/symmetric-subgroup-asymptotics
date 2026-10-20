import SymmetricSubgroupAsymptotics.BinaryCoordinateRegistry
import SymmetricSubgroupAsymptotics.BinaryFiniteCoordinateAction
import SymmetricSubgroupAsymptotics.BinaryNormalGeneratorChecks
import SymmetricSubgroupAsymptotics.GeneratedTopNormals.Pilot046

/-! Complete invariant axes for one literal correlated flip module.
Reversible charts, actual generator stability and sparse orbit joins are
kernel checked. No normal-lift enumeration is a proof premise. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryKernelAxes077
abbrev Source := FiniteGroupRow 16
local instance pilotBaseGroup : Group Source := BinaryTopSource046.group

def generators (j : Fin 3) : Source :=
  ⟨BinaryTopSource046.certificate.next BinaryTopSource046.certificate.identity j⟩

theorem generators_full : Subgroup.closure (Set.range generators)=⊤ :=
  BinaryTopSource046.certificate.row_generators_full BinaryTopSource046.rows_injective BinaryTopSource046.prevRow BinaryTopSource046.prev_checked

def permutation : Source →* Equiv.Perm (Fin 8) :=
  (Subgroup.closure (Set.range BinaryTopSource046.generators)).subtype.comp BinaryTopSource046.originalEquiv.toMonoidHom
def action : Representation (ZMod 2) Source (Fin 8 → ZMod 2) :=
  (binaryPermutationRepresentation 8).comp permutation

/-- Numeric rows are checked once against the exact original encoding. -/
def rowPermutation (g : Source) : Equiv.Perm (Fin 8) where
  toFun x := ((if g.index.val < 8 then (if g.index.val < 4 then (if g.index.val < 2 then (if g.index.val < 1 then #[7,4,5,6,1,2,3,0] else #[6,5,4,7,1,2,3,0]) else (if g.index.val < 3 then #[5,6,7,4,0,3,2,1] else #[4,7,6,5,0,3,2,1])) else (if g.index.val < 6 then (if g.index.val < 5 then #[5,6,7,4,3,0,1,2] else #[4,7,6,5,3,0,1,2]) else (if g.index.val < 7 then #[7,4,5,6,2,1,0,3] else #[6,5,4,7,2,1,0,3]))) else (if g.index.val < 12 then (if g.index.val < 10 then (if g.index.val < 9 then #[2,3,0,1,7,6,5,4] else #[1,0,3,2,7,6,5,4]) else (if g.index.val < 11 then #[2,3,0,1,6,7,4,5] else #[1,0,3,2,6,7,4,5])) else (if g.index.val < 14 then (if g.index.val < 13 then #[3,2,1,0,5,4,7,6] else #[0,1,2,3,5,4,7,6]) else (if g.index.val < 15 then #[3,2,1,0,4,5,6,7] else #[0,1,2,3,4,5,6,7])))) : Array (Fin 8))[x.val]!
  invFun x := ((if g.index.val < 8 then (if g.index.val < 4 then (if g.index.val < 2 then (if g.index.val < 1 then #[7,4,5,6,1,2,3,0] else #[7,4,5,6,2,1,0,3]) else (if g.index.val < 3 then #[4,7,6,5,3,0,1,2] else #[4,7,6,5,0,3,2,1])) else (if g.index.val < 6 then (if g.index.val < 5 then #[5,6,7,4,3,0,1,2] else #[5,6,7,4,0,3,2,1]) else (if g.index.val < 7 then #[6,5,4,7,1,2,3,0] else #[6,5,4,7,2,1,0,3]))) else (if g.index.val < 12 then (if g.index.val < 10 then (if g.index.val < 9 then #[2,3,0,1,7,6,5,4] else #[1,0,3,2,7,6,5,4]) else (if g.index.val < 11 then #[2,3,0,1,6,7,4,5] else #[1,0,3,2,6,7,4,5])) else (if g.index.val < 14 then (if g.index.val < 13 then #[3,2,1,0,5,4,7,6] else #[0,1,2,3,5,4,7,6]) else (if g.index.val < 15 then #[3,2,1,0,4,5,6,7] else #[0,1,2,3,4,5,6,7])))) : Array (Fin 8))[x.val]!
  left_inv := by revert g; decide +kernel
  right_inv := by revert g; decide +kernel
private theorem row_checked : ∀ (g : Source) (x : Fin 8),
    rowPermutation g x=finFunctionFinEquiv.symm (BinaryTopSource046.certificate.rows g.index) x := by decide +kernel

theorem rowPermutation_eq_original (g : Source) :
    rowPermutation g=(BinaryTopSource046.originalEquiv g : Equiv.Perm (Fin 8)) := by
  apply Equiv.ext
  intro x
  change rowPermutation g x=BinaryTopSource046.certificate.toCayley.elements g.index x
  rw [BinaryTopSource046.certificate.permutation_elements_apply]
  exact row_checked g x

theorem permutation_eq_row (g : Source) : permutation g=rowPermutation g :=
  (rowPermutation_eq_original g).symm
theorem rowPermutation_injective : Function.Injective rowPermutation := by
  intro g h he
  apply BinaryTopSource046.originalEquiv.injective
  apply Subtype.ext
  simpa only [rowPermutation_eq_original] using he
theorem rowPermutation_mul (g h : Source) :
    rowPermutation (g*h)=rowPermutation g*rowPermutation h := by
  simpa only [permutation_eq_row] using permutation.map_mul g h
theorem row_mul_eq_iff (g h k : Source) :
    g*h=k ↔ rowPermutation g*rowPermutation h=rowPermutation k := by
  constructor
  · intro he
    simpa only [rowPermutation_mul] using congrArg rowPermutation he
  · intro he
    apply rowPermutation_injective
    simpa only [rowPermutation_mul] using he
theorem row_commute_iff (g h : Source) :
    g*h=h*g ↔ rowPermutation g*rowPermutation h=rowPermutation h*rowPermutation g := by
  constructor
  · intro he
    simpa only [rowPermutation_mul] using congrArg rowPermutation he
  · intro he
    apply rowPermutation_injective
    simpa only [rowPermutation_mul] using he

theorem action_numeric (g : Source) :
    action g=binaryPermutationRepresentation 8 (rowPermutation g) := by
  rw [rowPermutation_eq_original]
  rfl
theorem action_inverse_numeric (g : Source) :
    action g⁻¹=binaryPermutationRepresentation 8 (rowPermutation g)⁻¹ := by
  change binaryPermutationRepresentation 8 (permutation g⁻¹)=_
  rw [map_inv,rowPermutation_eq_original]
  rfl

end SymmetricSubgroupAsymptotics.BinaryKernelAxes077
