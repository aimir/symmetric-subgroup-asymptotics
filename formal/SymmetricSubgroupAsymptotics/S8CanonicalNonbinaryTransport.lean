import SymmetricSubgroupAsymptotics.PrimitiveAffineEightCanonicalCatalogue
import SymmetricSubgroupAsymptotics.S8Sylow128SelectedRows
import SymmetricSubgroupAsymptotics.FiniteSubgroupAdjunctionCoverage
import Mathlib.GroupTheory.PGroup
import Mathlib.Tactic.FinCases

/-! Actual point-conjugacy transport into the fixed canonical degree-eight
family. A binary seed row is excluded only by the stated nonbinary source
hypothesis; the other selected H128 targets have literal canonical indices. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics.S8CanonicalNonbinaryTransport
open FiniteSubgroupAdjunctionCoverage
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

abbrev Ambient := Equiv.Perm (Fin 8)

theorem isPGroup_of_conjugate (T Q : Subgroup Ambient) (c : Ambient)
    (hc : MulAut.conj c • T = Q) (hQ : IsPGroup 2 Q) : IsPGroup 2 T := by
  let e : T ≃* Q := ((MulAut.conj c).subgroupMap T).trans
    (MulEquiv.subgroupCongr
      (show T.map (MulAut.conj c).toMonoidHom = Q from hc))
  exact hQ.of_equiv e.symm

theorem sylow_seed_isPGroup : IsPGroup 2 S8Sylow128LeftCosets.H :=
  IsPGroup.of_card (n := 7) (by
    change Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T35.generators)) = 128
    exact BinaryMenuCayley8T35.exact_card)

theorem of_large_covered (T : Subgroup Ambient) (hnot : ¬ IsPGroup 2 T)
    (hcovered : Covered S8Sylow128SelectedRows.rows T) :
    ∃ j : Fin 24, ∃ c : Ambient, MulAut.conj c • T = DegreeEightCanonicalCatalogue.canonical j := by
  obtain ⟨i, c, hc⟩ := hcovered
  fin_cases i
  · change MulAut.conj c • T = S8Sylow128LeftCosets.H at hc
    exact False.elim (hnot (isPGroup_of_conjugate T _ c hc sylow_seed_isPGroup))
  · exact ⟨16, c, hc⟩
  · exact ⟨7, c, hc⟩
  · exact ⟨9, c, hc⟩
  · exact ⟨23, c, hc⟩

end SymmetricSubgroupAsymptotics.S8CanonicalNonbinaryTransport

end
