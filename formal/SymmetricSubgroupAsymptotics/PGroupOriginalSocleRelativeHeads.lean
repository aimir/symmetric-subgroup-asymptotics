import SymmetricSubgroupAsymptotics.BinaryCoverage
import SymmetricSubgroupAsymptotics.PrimeCentralSocleRelativeHead

/-! All original quotient socles of a p-group are controlled by its actual
ambient relative heads. Minimal normals remain central in each quotient. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PGroupOriginalSocleRelativeHeads
variable (p : ℕ) [Fact p.Prime]
variable {G : Type} [Group G] [Finite G]

 theorem minimalNormal_le_center (hG : IsPGroup p G)
    (M : Subgroup G) (hM : IsMinimalNormalSubgroup M) : M≤Subgroup.center G := by
  letI : M.Normal := hM.1
  obtain ⟨z,hzM,hzc,hzo⟩ := pGroup_normal_contains_central_prime hG M hM.2.1
  have hzne : z≠1 := by
    intro hz
    have hp : p=1 := by simpa only [hz,orderOf_one] using hzo.symm
    exact (Fact.out : Nat.Prime p).ne_one hp
  let Z := M ⊓ Subgroup.center G
  have hZ : Z≠⊥ := by
    intro hb
    have hz : z∈Z := ⟨hzM,hzc⟩
    rw [hb] at hz
    exact hzne (Subgroup.mem_bot.mp hz)
  have he : Z=M := hM.2.2 Z inferInstance hZ inf_le_left
  exact he.symm.le.trans inf_le_right

 theorem socle_eq_centralPrimeSoclePart (hG : IsPGroup p G) :
    finiteGroupSocle G=centralPrimeSoclePart p G := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro x ⟨M,hM,hx⟩
    exact minimalNormal_le_minimalNormalSoclePart
      (fun K => K≤Subgroup.center G ∧ IsPGroup p K) M hM
      ⟨minimalNormal_le_center p hG M hM,hG.to_subgroup M⟩ hx
  · exact minimalNormalSoclePart_le_finiteGroupSocle G _

 theorem quotientSocle (hG : IsPGroup p G) (slots : ℕ)
    (hhead : ∀ K : {K : Subgroup G // K.Normal},
      Module.finrank (ZMod p) (primeRelativeCharacters p K.1) ≤ slots)
    (N : Subgroup G) [N.Normal] : SocleNormalGeneratorBound (G ⧸ N) slots := by
  have h := centralPrimeSoclePart_normalGen_le_of_allRelativeHeads p slots hhead
    (⟨N,inferInstance⟩ : {N : Subgroup G // N.Normal})
  rw [← socle_eq_centralPrimeSoclePart p (hG.to_quotient N)] at h
  exact (socleNormalGeneratorBound_iff_normalGen_le _ _).mpr h
end SymmetricSubgroupAsymptotics.PGroupOriginalSocleRelativeHeads
