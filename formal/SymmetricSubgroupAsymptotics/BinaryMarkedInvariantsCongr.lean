import SymmetricSubgroupAsymptotics.PrimeSubdirectNormalRank
import SymmetricSubgroupAsymptotics.RelativeAmbientTransport
import SymmetricSubgroupAsymptotics.BinarySubdirectInflation

/-! The three carrier marks are invariant under an actual original group
equivalence. The derived-normal maximum transports actual attaining normals
and their whole-ambient actions. The H² defect uses its checked exact
identification with the relative head of the actual evaluation kernel.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

section Prime
variable (p : ℕ) [Fact p.Prime]
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

private theorem primeDerivedNormalRank_le_equiv (e : G ≃* H) :
    primeDerivedNormalRank p G ≤ primeDerivedNormalRank p H := by
  obtain ⟨M,hM,hderived,hattain⟩ := primeDerivedNormalRank_attained p G
  letI : M.Normal := hM
  letI : (M.map e.toMonoidHom).Normal := Subgroup.Normal.map hM _ e.surjective
  have hcomm : (commutator G).map e.toMonoidHom = commutator H := by
    rw [map_commutator_eq,MonoidHom.range_eq_top.mpr e.surjective,← commutator_def]
  have himage : M.map e.toMonoidHom ≤ commutator H :=
    (Subgroup.map_mono hderived).trans_eq hcomm
  have hdim := (relativeCharacterAmbientCongr p e M (M.map e.toMonoidHom) rfl).finrank_eq
  calc
    _ = Module.finrank (ZMod p) (primeRelativeCharacters p M) := hattain.symm
    _ = Module.finrank (ZMod p) (primeRelativeCharacters p (M.map e.toMonoidHom)) :=
      hdim.symm
    _ ≤ _ := primeRelativeHead_le_normalHeadMax p (commutator H)
      (M.map e.toMonoidHom) himage

/-- Both directions map actual derived normals and preserve their full
ambient invariant characters. No monotonicity of absolute subgroup rank is used. -/
theorem primeDerivedNormalRank_congr (e : G ≃* H) :
    primeDerivedNormalRank p G = primeDerivedNormalRank p H :=
  le_antisymm (primeDerivedNormalRank_le_equiv p e)
    (primeDerivedNormalRank_le_equiv p e.symm)
end Prime

theorem binaryCharacterRank_congr {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    binaryCharacterRank G = binaryCharacterRank H := primeCharacter_finrank_congr 2 e

/-- This transports the actual terminal inflation-kernel dimension,
through the exact evaluation kernels and their whole-ambient conjugation. -/
theorem terminalRestrictedInflationKernel_finrank_congr
    {G H : Type} [Group G] [Group H] [Finite G] [Finite H] (e : G ≃* H) :
    Module.finrank (ZMod 2) (terminalRestrictedInflationKernel G) =
      Module.finrank (ZMod 2) (terminalRestrictedInflationKernel H) := by
  rw [terminalRestrictedInflationKernel_finrank_eq_primeRelativeHead G,
    terminalRestrictedInflationKernel_finrank_eq_primeRelativeHead H]
  exact (relativeCharacterAmbientCongr 2 e
    (primeAbelianizationGroupMap 2 G).ker (primeAbelianizationGroupMap 2 H).ker
    (primeAbelianizationGroupMap_ker_map 2 e.toMonoidHom e.surjective)).finrank_eq.symm

end SymmetricSubgroupAsymptotics
