import SymmetricSubgroupAsymptotics.BinaryBySymmetricThree
import SymmetricSubgroupAsymptotics.NaturalFourNormalChains
import SymmetricSubgroupAsymptotics.CoprimeCyclicQuotientSocles

/-! A uniform-one binary kernel over the literal symmetric three group
has a normally cyclic whole socle. The binary socle cannot project to a
nontrivial normal binary subgroup of S3; the odd socle costs one position,
and the two prime types share that same position. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryBySymmetricThreeSocleOne
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

 theorem normal_binary_eq_bot (H : Subgroup (Equiv.Perm (Fin 3)))
    (hH : H.Normal) (hbinary : IsPGroup 2 H) : H=⊥ := by
  let A := alternatingGroup (Fin 3)
  have hcard : Nat.card A=3 := by
    dsimp only [A]
    rw [nat_card_alternatingGroup]
    norm_num [Nat.card_fin]
  have hternary : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by simpa using hcard)
  have hd : Disjoint H A := IsPGroup.disjoint_of_ne 2 3 (by decide) H A hbinary hternary
  rcases NaturalFourNormalChains.symmetric_three_normal_total H A hH inferInstance with hHA | hAH
  · apply le_antisymm _ bot_le
    intro x hx
    exact (disjoint_iff_inf_le.mp hd) ⟨hx,hHA hx⟩
  · have hAb : A=⊥ := by
      apply le_antisymm _ bot_le
      intro x hx
      exact (disjoint_iff_inf_le.mp hd) ⟨hAH hx,hx⟩
    have hone : Nat.card A=1 := (Subgroup.card_eq_one).mpr hAb
    omega

 theorem socle_one {Q : Type} [Group Q] [Finite Q]
    (beta : Q →* Equiv.Perm (Fin 3)) (hbeta : Function.Surjective beta)
    (hker : IsPGroup 2 beta.ker) {a : ℕ} (hcard : Nat.card Q∣2^a*3)
    (hgen : ∀ H : Subgroup Q, H.Normal → H≤beta.ker → MarkedC4.normalGen H≤1) :
    SocleNormalGeneratorBound Q 1 := by
  let P := minimalNormalSoclePart Q (fun M => IsPGroup 2 M)
  have hP : IsPGroup 2 P := primePrimarySoclePart_isPGroup 2 Q
  letI : (P.map beta).Normal := Subgroup.Normal.map inferInstance beta hbeta
  have hbot : P.map beta=⊥ := normal_binary_eq_bot _ inferInstance (hP.map beta)
  have hle : P≤beta.ker := (Subgroup.map_eq_bot_iff (H := P) (f := beta)).mp hbot
  have hprimary : MarkedC4.normalGen P≤1 := hgen P inferInstance hle
  have hother := nonbinarySocle_normalGen_le_one_of_binary_kernel_symmetricThree beta hker hcard
  apply (socleNormalGeneratorBound_iff_normalGen_le Q 1).mpr
  exact (normalGen_finiteGroupSocle_le_max_primePrimaryParts 2 Q).trans
    (max_le hprimary hother)

end SymmetricSubgroupAsymptotics.BinaryBySymmetricThreeSocleOne
