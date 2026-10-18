import SymmetricSubgroupAsymptotics.NaturalFourNormalChains
import SymmetricSubgroupAsymptotics.BinaryFourCanonicalNaturalChart
import SymmetricSubgroupAsymptotics.BinaryFourA4NormalRelativeHead
import SymmetricSubgroupAsymptotics.RelativeAmbientSubgroup
import SymmetricSubgroupAsymptotics.RelativeAmbientTransport

/-! Every proper original normal image in the literal S4 has zero
ambient binary relative head. The full-image sign contribution is kept
separate by the signed-kernel argument. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwelvePointRemainingStructural
local instance symmetricTop_binaryPrimeFact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem proper_normal_le_alternating
    (M : Subgroup (Equiv.Perm (Fin 4))) [M.Normal] (hne : M ≠ ⊤) :
    M ≤ alternatingGroup (Fin 4) := by
  rcases NaturalFourNormalChains.symmetric_normal_total M (alternatingGroup (Fin 4))
      inferInstance inferInstance with h | h
  · exact h
  · have hd : M.index ∣ 2 := by
      simpa only [alternatingGroup.index_eq_two] using Subgroup.index_dvd_of_le h
    have hi : M.index = 2 := ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left
      (fun he => hne (Subgroup.index_eq_one.mp he))
    have hr := Subgroup.relIndex_mul_index h
    rw [hi, alternatingGroup.index_eq_two] at hr
    have hr1 : (alternatingGroup (Fin 4)).relIndex M = 1 := by omega
    exact Subgroup.relIndex_eq_one.mp hr1

theorem alternating_normal_binary_relative_head_zero
    (M : Subgroup (alternatingGroup (Fin 4))) [M.Normal] :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 M) = 0 := by
  let e := BinaryFourCanonicalInducedChart.naturalGroupEquiv
  let J := M.map e.symm.toMonoidHom
  letI : J.Normal := Subgroup.Normal.map inferInstance _ e.symm.surjective
  have hJ : J.map e.toMonoidHom = M := by
    change (M.map e.symm.toMonoidHom).map e.toMonoidHom = M
    rw [Subgroup.map_map]
    have he : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id _ := by
      apply MonoidHom.ext
      intro x
      exact e.apply_symm_apply x
    rw [he, Subgroup.map_id]
  exact (relativeCharacterAmbientCongr 2 e J M hJ).finrank_eq.trans
    (BinaryFourA4NormalRelativeHead.normal_relative_head_zero J)

theorem proper_normal_binary_relative_head_zero
    (M : Subgroup (Equiv.Perm (Fin 4))) [M.Normal] (hne : M ≠ ⊤) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 M) = 0 := by
  have hle := proper_normal_le_alternating M hne
  have h := primeRelativeHead_inf_le_subgroupOf 2 M (alternatingGroup (Fin 4))
  have hz := alternating_normal_binary_relative_head_zero
    (M.subgroupOf (alternatingGroup (Fin 4)))
  rw [hz] at h
  have h' : Module.finrank (ZMod 2) (primeRelativeCharacters 2 M) ≤ 0 := by
    let e : Equiv.Perm (Fin 4) ≃* Equiv.Perm (Fin 4) := MulEquiv.refl _
    have he : (M ⊓ alternatingGroup (Fin 4)).map e.toMonoidHom = M := by
      change (M ⊓ alternatingGroup (Fin 4)).map (MonoidHom.id _) = M
      rw [Subgroup.map_id]
      exact inf_eq_left.mpr hle
    exact (relativeCharacterAmbientCongr 2 e (M ⊓ alternatingGroup (Fin 4)) M he).finrank_eq.le.trans h
  exact Nat.eq_zero_of_le_zero h'

end SymmetricSubgroupAsymptotics.TwelvePointRemainingStructural
