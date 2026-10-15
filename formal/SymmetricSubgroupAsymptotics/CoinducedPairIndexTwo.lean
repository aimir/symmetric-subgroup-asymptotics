import SymmetricSubgroupAsymptotics.CoinducedPairFiltration
import Mathlib.GroupTheory.IndexNormal

/-! Every actual subgroup of relative index two supplies the two-coset
identities used by the binary coinduced filtration. No order-two lift or
splitting of the extension is required. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CoinducedPairFiltration

variable {G : Type} [Group G] (H L : Subgroup G) (hHL : H ≤ L)

/-- An index-two inclusion gives the exact two-coset data; the chosen swap
may have higher order, and only its square is required to lie in H. -/
def TwoCosetData.ofRelativeIndexTwo (hindex : H.relIndex L = 2) :
    TwoCosetData H L hHL := by
  classical
  refine Classical.choice ?_
  let K : Subgroup L := H.subgroupOf L
  have hK : K.index = 2 := hindex
  letI : K.Normal := K.normal_of_index_eq_two hK
  obtain ⟨a, _ha, hcover⟩ := K.index_eq_two_iff_exists_notMem_and'.mp hK
  refine ⟨{
    swap := a⁻¹
    inverse_conjugate_mem := ?_
    square_mem := ?_
    decompose := ?_ }⟩
  · intro h
    have hc := Subgroup.Normal.conj_mem (H := K) inferInstance
      (Subgroup.inclusion hHL h) h.property a
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] using hc
  · exact K.mul_self_mem_of_index_two hK a⁻¹
  · intro l
    rcases hcover l with hl | hl
    · refine ⟨⟨((a * l : L) : G), hl⟩, Or.inr ?_⟩
      apply Subtype.ext
      change (l : G) = (a : G)⁻¹ * ((a : G) * (l : G))
      group
    · exact ⟨⟨(l : G), hl⟩, Or.inl rfl⟩

end SymmetricSubgroupAsymptotics.CoinducedPairFiltration

end
