import SymmetricSubgroupAsymptotics.CFSGNormalizerCenterAtomFamilies
import SymmetricSubgroupAsymptotics.CFSGNormalizerCenterAtomsEquiv
import SymmetricSubgroupAsymptotics.CFSGSymplecticCenterAtomCount
import SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryNaturalRootAtom
import SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryProjectiveEquiv
import SymmetricSubgroupAsymptotics.CFSGSymplecticProjectiveNaturalRootLines
import SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotentSylow

/-! At most three actual inner-conjugacy families can occur as
automorphism images of the original projective natural-root family
in characteristic two. The proof uses the same actual Sylow and the
proved elementary/projective isomorphism, not an automorphism-lift premise. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
open CFSGSymplecticSerreMatrices CFSGSymplecticTransvectionGeometry CFSGNormalizerCenterAtoms
variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem binaryChar_naturalRoot_family_image_card_le_three (r : ℕ) (hr : 0 < r) :
    Nat.card (Set.range (fun f : MulAut (elementaryProjective K (r + 1)) =>
      innerFamily ((projectiveNaturalRootLine r hr
        (Pi.single (Sum.inl (0 : Fin (r + 1))) 1)).map f.toMonoidHom))) ≤ 3 := by
  letI binaryRootFamilyImages_factTwo : Fact (Nat.Prime 2) := ⟨by decide⟩
  let e := binaryProjectiveEquiv K r
  let v : Index (r + 1) → K := Pi.single (Sum.inl (0 : Fin (r + 1))) 1
  let L := actualNaturalRootLine r hr v
  let P : Sylow 2 (elementaryProjective K (r + 1)) :=
    (unipotentSylow K 2 r hr).mapSurjective (f := e.toMonoidHom) e.surjective
  have hline : L.map e.toMonoidHom = projectiveNaturalRootLine r hr v := by
    ext x
    constructor
    · rintro ⟨y, ⟨a, hay⟩, hyx⟩
      refine ⟨a, ?_⟩
      change e (actualNaturalRootHom r hr v a) = x
      exact (congrArg e hay).trans hyx
    · rintro ⟨a, ha⟩
      exact ⟨actualNaturalRootHom r hr v a, ⟨a, rfl⟩, ha⟩
  have hA : IsAtom (P : Subgroup (elementaryProjective K (r + 1)))
      (projectiveNaturalRootLine r hr v) := by
    have h := map_isAtom e (unipotent K (r + 1)) L
      (binaryChar_naturalRoot_is_normalizerCenterAtom r hr)
    rwa [hline] at h
  have hcard : Nat.card {J : Subgroup (elementaryProjective K (r + 1)) //
      IsAtom (P : Subgroup (elementaryProjective K (r + 1))) J} ≤ 3 := by
    change Nat.card {J : Subgroup (elementaryProjective K (r + 1)) //
      IsAtom ((unipotent K (r + 1)).map e.toMonoidHom) J} ≤ 3
    rw [atom_card_map e (unipotent K (r + 1))]
    by_cases hq : Nat.card K = 2
    · exact binaryField_centerAtom_card_le_three r hr hq
    · have htwo : 1 < Nat.card K := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
      exact (largerField_centerAtom_card_le_two r hr (by omega)).trans (by decide : 2 ≤ 3)
  exact (family_image_card_le_atom_card 2 P (projectiveNaturalRootLine r hr v) hA).trans hcard

end SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
