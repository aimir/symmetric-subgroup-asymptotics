import SymmetricSubgroupAsymptotics.CFSGNormalizerCenterAtomCount
import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic.Group

/-! An automorphism image of a fixed intrinsic Sylow-centre atom
can be aligned to an atom of the same fixed Sylow by one actual inner
conjugator. Thus its inner-conjugacy family has at most as many
automorphism images as there are actual local atoms. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormalizerCenterAtoms
variable {G : Type*} [Group G]

def innerFamily (H : Subgroup G) : Set (Subgroup G) :=
  {J | ∃ g : G, J = H.map (MulAut.conj g).toMonoidHom}

private theorem map_conj_map (H : Subgroup G) (g x : G) :
    (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x).toMonoidHom =
      H.map (MulAut.conj (x * g)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext y
  change x * (g * y * g⁻¹) * x⁻¹ = (x * g) * y * (x * g)⁻¹
  group

private theorem map_conj_one (H : Subgroup G) :
    H.map (MulAut.conj (1 : G)).toMonoidHom = H := by
  have he : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    ext x
    change (1 : G) * x * (1 : G)⁻¹ = x
    simp only [one_mul, inv_one, mul_one]
  rw [he, Subgroup.map_id]

theorem innerFamily_conjugate (H : Subgroup G) (g : G) :
    innerFamily (H.map (MulAut.conj g).toMonoidHom) = innerFamily H := by
  ext J
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x * g, hx.trans (map_conj_map H g x)⟩
  · rintro ⟨x, hx⟩
    refine ⟨x * g⁻¹, ?_⟩
    rw [map_conj_map, mul_assoc, inv_mul_cancel, mul_one]
    exact hx

theorem exists_fixed_sylow_atom_image_family [Finite G] (p : ℕ) [Fact p.Prime]
    (P : Sylow p G) (H : Subgroup G) (hH : IsAtom (P : Subgroup G) H)
    (f : MulAut G) :
    ∃ J : {J : Subgroup G // IsAtom (P : Subgroup G) J},
      innerFamily (H.map f.toMonoidHom) = innerFamily J.val := by
  let Q : Sylow p G := P.mapSurjective (f := f.toMonoidHom) f.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  have hP : (P : Subgroup G).map f.toMonoidHom =
      (P : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    have he := congrArg (fun R : Sylow p G => (R : Subgroup G)) hg
    exact he.symm
  let J := (H.map f.toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom
  have hreset : ((P : Subgroup G).map f.toMonoidHom).map
      (MulAut.conj g⁻¹).toMonoidHom = (P : Subgroup G) := by
    rw [hP, map_conj_map, inv_mul_cancel, map_conj_one]
  have hJ := map_isAtom (MulAut.conj g⁻¹) _ _ (map_isAtom f _ _ hH)
  rw [hreset] at hJ
  refine ⟨⟨J, hJ⟩, ?_⟩
  exact (innerFamily_conjugate (H.map f.toMonoidHom) g⁻¹).symm

theorem family_image_card_le_atom_card [Finite G] (p : ℕ) [Fact p.Prime]
    (P : Sylow p G) (H : Subgroup G) (hH : IsAtom (P : Subgroup G) H) :
    Nat.card (Set.range (fun f : MulAut G => innerFamily (H.map f.toMonoidHom))) ≤
      Nat.card {J : Subgroup G // IsAtom (P : Subgroup G) J} := by
  let Images := Set.range (fun f : MulAut G => innerFamily (H.map f.toMonoidHom))
  have hex (x : Images) : ∃ J : {J : Subgroup G // IsAtom (P : Subgroup G) J},
      x.val = innerFamily J.val := by
    obtain ⟨f, hf⟩ := x.property
    obtain ⟨J, hJ⟩ := exists_fixed_sylow_atom_image_family p P H hH f
    exact ⟨J, hf.symm.trans hJ⟩
  let F : Images → {J : Subgroup G // IsAtom (P : Subgroup G) J} :=
    fun x => Classical.choose (hex x)
  have hF (x : Images) : x.val = innerFamily (F x).val := Classical.choose_spec (hex x)
  apply Nat.card_le_card_of_injective F
  intro x y he
  apply Subtype.ext
  exact (hF x).trans ((congrArg (fun J => innerFamily J.val) he).trans (hF y).symm)

end SymmetricSubgroupAsymptotics.CFSGNormalizerCenterAtoms
