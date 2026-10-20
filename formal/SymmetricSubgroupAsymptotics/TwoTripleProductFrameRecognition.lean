import SymmetricSubgroupAsymptotics.TwoTriplePhysicalPermutationCover
import SymmetricSubgroupAsymptotics.ProductBlockFrameGenerators

/-! An actual two-triple product frame gives a point-conjugate subgroup
of the standard ternary local wreath. The original subgroup is retained. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.TwoTripleProductFrameRecognition
open TwoTriplePhysicalPermutationCover

def standardChart : Fin 2 × ZMod 3 ≃ Fin 6 where
  toFun z := point z.1 z.2
  invFun x := (block x,coordinate x)
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem block_point : ∀ (i : Fin 2) (x : ZMod 3),
    block (point i x) = i := by decide +kernel

variable {P : Subgroup (Equiv.Perm (Fin 6))}
  (F : ProductBlockFrame P (Fin 2) (ZMod 3))

def conjugator : Equiv.Perm (Fin 6) := F.frame.symm.trans standardChart

private theorem block_conjugator (x : Fin 6) :
    block (conjugator F x) = (F.frame.symm x).1 :=
  block_point _ _

theorem conjugate_le : MulAut.conj (conjugator F) • P ≤
    SixPairLocalWreathSocles.literalAction.range := by
  intro g hg
  rw [Subgroup.pointwise_smul_def] at hg
  obtain ⟨p,hp,rfl⟩ := hg
  apply TwoTriplePhysicalPermutationCover.cover _ (F.top ⟨p,hp⟩)
  intro x
  change block (conjugator F (p ((conjugator F).symm x))) =
    F.top ⟨p,hp⟩ (block x)
  rw [block_conjugator]
  have h := F.intertwine ⟨p,hp⟩ (F.frame.symm ((conjugator F).symm x))
  simp only [F.frame.apply_symm_apply] at h
  rw [h]
  congr 1
  have hb := block_conjugator F ((conjugator F).symm x)
  simpa only [Equiv.apply_symm_apply] using hb.symm

end SymmetricSubgroupAsymptotics.TwoTripleProductFrameRecognition
