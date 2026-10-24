import SymmetricSubgroupAsymptotics.CFSGSuzukiQuadraticTorusStabilizerIndex
import SymmetricSubgroupAsymptotics.CFSGSuzukiBorelSemidirectHom
import SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupDegree

/-! Every proper subgroup of the SAME actual Suzuki matrix model has
the quadratic/torus lower index. Inherited simplicity moves an actual
nonzero central parameter; one pulled-back stabilizer supplies all three
layers of the preceding proof, in every defining field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiQuadraticTorusIndex
open CFSGSuzukiFieldParameters CFSGSuzukiUnipotent CFSGSuzukiCentralExtensionLayers
open CFSGSuzukiCentralAnnihilatorIndex CFSGSuzukiQuadraticTorusStabilizerIndex
open CFSGSuzukiBorelSemidirectHom CFSGSuzukiCentralPermutationDegree

theorem suzuki_quadratic_torus_le_proper_index (m : ℕ) (_hm : 1 ≤ m)
    [IsSimpleGroup (CFSG.Models.Suzuki m)]
    (H : Subgroup (CFSG.Models.Suzuki m)) (hH : H ≠ ⊤) :
    (2^(2*m+1)-1)*2^(m+1) ≤ H.index := by
  let c : Multiplicative (Field m) := Multiplicative.ofAdd 1
  have hc : centralModelHom m c ≠ 1 := by
    intro he
    have hh : c = 1 := centralModelHom_injective m
      (he.trans (map_one (centralModelHom m)).symm)
    exact one_ne_zero (congrArg (fun z : Multiplicative (Field m) => z.toAdd) hh)
  obtain ⟨x, hx⟩ := CFSGConjugateSubgroupDegree.exists_moved_coset_of_ne_one H hH _ hc
  letI : MulAction (Borel m) (CFSG.Models.Suzuki m ⧸ H) :=
    MulAction.compHom _ (extensionHom m)
  let M : Subgroup (Borel m) := MulAction.stabilizer (Borel m) x
  have hM : ¬(centralHom m).range ≤ M.comap SemidirectProduct.inl := by
    intro h
    have hn := h ⟨c, rfl⟩
    change SemidirectProduct.inl (centralHom m c) • x = x at hn
    apply hx
    simpa only [MulAction.compHom_smul_def, extensionHom_central] using hn
  have hb : (Nat.card (Field m)-1)*2^(m+1) ≤ Nat.card (CFSG.Models.Suzuki m ⧸ H) := by
    calc
      _ ≤ M.index := quadratic_torus_le_index m M hM
      _ = (MulAction.orbit (Borel m) x).ncard := MulAction.index_stabilizer _ _
      _ ≤ Nat.card (CFSG.Models.Suzuki m ⧸ H) := Set.ncard_le_card _
  rw [field_card] at hb
  simpa only [Subgroup.index_eq_card] using hb

end SymmetricSubgroupAsymptotics.CFSGSuzukiQuadraticTorusIndex
