import SymmetricSubgroupAsymptotics.FiniteSubgroupAdjunctionCoverage
import SymmetricSubgroupAsymptotics.FiniteGeneratorEquivWordCertificate
import Mathlib.Data.Fin.VecNotation

/-! Bidirectional words check each local subgroup-adjunction equality,
without evaluating a subgroup closure or assuming a catalogue match. -/

set_option autoImplicit false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics.FiniteSubgroupAdjunctionCoverage

variable {G : Type*} [Group G] {n m : ℕ}

theorem adjoin_eq_of_words (source : Fin n → G) (target : Fin m → G)
    (g c : G)
    (C : FiniteGeneratorEquivWordCertificate (MulAut.conj c)
      (Matrix.vecCons g source) target) :
    MulAut.conj c •
      (Subgroup.closure (Set.range source) ⊔ Subgroup.closure {g}) =
      Subgroup.closure (Set.range target) := by
  change (Subgroup.closure (Set.range source) ⊔ Subgroup.closure {g}).map
    (MulAut.conj c).toMonoidHom = _
  simpa only [Matrix.range_cons, Subgroup.closure_union, sup_comm] using
    C.map_closure_eq

end SymmetricSubgroupAsymptotics.FiniteSubgroupAdjunctionCoverage

end
