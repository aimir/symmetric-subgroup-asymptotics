import SymmetricSubgroupAsymptotics.DihedralFourOriginalAbelianAxes
import SymmetricSubgroupAsymptotics.SixPairDihedralSocles
import SymmetricSubgroupAsymptotics.FiniteGeneratorWord

/-! Four original tuples share a physical six-pair chart and literal
six-point dihedral coordinates. All words are evaluated in their actual
original subgroups. No original group closure is computed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.DihedralFourOriginalFrames
open DihedralFourOriginalAbelianAxes (generators U original)
open SixPairCyclicSymmetricSocles (cycle)
open SixPairDihedralSocles (reflection dihedralMap)

private def relabel : Fin 6 ≃ Fin 6 where
  toFun := ![0,3,4,1,2,5]
  invFun := ![0,3,4,1,2,5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pointChart (r : Fin 4) : Fin 6 × ZMod 2 ≃ Fin 12 :=
  if r.val<2 then SixPairCyclicSymmetricSocles.pointChart else
    (Equiv.prodCongr relabel (Equiv.refl (ZMod 2))).trans SixPairCyclicSymmetricSocles.pointChart
private def codes (r : Fin 4) : Fin 4 → DihedralGroup 6 :=
  if r.val<2 then ![.r 0,.r 0,.r 1,.sr 0] else if r=2 then
    ![.r 0,.r 4,.sr 2,.sr 5] else ![.r 0,.r 4,.sr 5,.sr 2]
def tops (r : Fin 4) (i : Fin 4) := dihedralMap (codes r i)
private theorem preserves : ∀ r i,
    BinaryPairFrame.Preserves (pointChart r) (generators r i) (tops r i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

def frame (r : Fin 4) : BinaryPairFrame (U r) (Fin 6) :=
  BinaryPairFrame.ofGenerators (pointChart r) (generators r) (tops r) (preserves r)
private theorem generator_top (r i : Fin 4) : (frame r).top (original r i)=tops r i :=
  BinaryPairFrame.ofGenerators_top_generator (pointChart r) (generators r) (tops r) (preserves r) i
private theorem alphabet_top (r : Fin 4) : (fun i => (frame r).top (original r i))=tops r :=
  funext (generator_top r)
private def cycleWord (r : Fin 4) : FiniteGeneratorWord (Fin 4) :=
  if r.val<2 then .generator 2 else .mul (.mul (.generator 2) (.generator 3)) (.generator 1)
private def fourth (w : FiniteGeneratorWord (Fin 4)) : FiniteGeneratorWord (Fin 4) :=
  .mul (.mul (.mul w w) w) w
private def reflectionWord (r : Fin 4) : FiniteGeneratorWord (Fin 4) :=
  if r.val<2 then .generator 3 else
    .mul (.generator (if r=2 then 2 else 3)) (fourth (cycleWord r))
def cycleElement (r : Fin 4) : U r := (cycleWord r).eval (original r)
def reflectionElement (r : Fin 4) : U r := (reflectionWord r).eval (original r)

theorem top_cycle (r : Fin 4) : (frame r).top (cycleElement r)=cycle := by
  calc
    (frame r).top (cycleElement r)=(cycleWord r).eval (fun i => (frame r).top (original r i)) :=
      FiniteGeneratorWord.map_eval (frame r).top (original r) (cycleWord r)
    _ = (cycleWord r).eval (tops r) := congrArg (fun g => (cycleWord r).eval g) (alphabet_top r)
    _ = cycle := by revert r; decide +kernel

theorem top_reflection (r : Fin 4) : (frame r).top (reflectionElement r)=reflection := by
  calc
    (frame r).top (reflectionElement r)=(reflectionWord r).eval (fun i => (frame r).top (original r i)) :=
      FiniteGeneratorWord.map_eval (frame r).top (original r) (reflectionWord r)
    _ = (reflectionWord r).eval (tops r) := congrArg (fun g => (reflectionWord r).eval g) (alphabet_top r)
    _ = reflection := by revert r; decide +kernel

theorem top_image (r : Fin 4) : (frame r).top.range=dihedralMap.range := by
  apply le_antisymm
  · rw [show (frame r).top.range=Subgroup.closure (Set.range (tops r)) from
      BinaryPairFrame.ofGenerators_top_range (pointChart r) (generators r) (tops r) (preserves r)]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨codes r i,rfl⟩
  · rw [SixPairDihedralSocles.dihedralMap_range]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    fin_cases i
    · exact Subgroup.one_mem _
    · exact ⟨cycleElement r,top_cycle r⟩
    · exact ⟨reflectionElement r,top_reflection r⟩

end SymmetricSubgroupAsymptotics.DihedralFourOriginalFrames
