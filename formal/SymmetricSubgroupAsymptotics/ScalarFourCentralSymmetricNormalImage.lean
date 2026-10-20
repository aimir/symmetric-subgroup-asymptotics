import SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates
import SymmetricSubgroupAsymptotics.NaturalThreeNormalClassification

/-! For an ACTUAL S3 top, every nontrivial normal image contains the
selected cubic. An arbitrary group of order six is not classified here. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates
variable {Q T H : Type} [Group Q] [Group T] [Group H] {c d : ℕ}
  (D : ScalarFourCentralTopCoordinates Q T c d)

private theorem cube_even : ∀ x : Equiv.Perm (Fin 3), x^3=1 →
    x∈alternatingGroup (Fin 3) := by
  change ∀ x : Equiv.Perm (Fin 3), x^3=1 → Equiv.Perm.sign x=1
  decide +kernel

theorem symmetric_normal_image_kills_cubic (e : T ≃* Equiv.Perm (Fin 3))
    (hcubic : D.cubic^3=1) (f : Q →* H) (hker : ¬f.ker≤D.top.ker) :
    ∃ n : Q, f n=1 ∧ D.top n=D.cubic := by
  let pi : Q →* Equiv.Perm (Fin 3) := e.toMonoidHom.comp D.top
  have hpi : Function.Surjective pi := e.surjective.comp D.top_surjective
  let R : Subgroup (Equiv.Perm (Fin 3)) := f.ker.map pi
  have hR : R.Normal := Subgroup.Normal.map inferInstance pi hpi
  have hn : R≠⊥ := by
    intro hz
    obtain ⟨g,hgf,hgt⟩ := Set.not_subset.mp hker
    have hgR : pi g∈R := ⟨g,hgf,rfl⟩
    rw [hz] at hgR
    have hg1 : e (D.top g)=1 := hgR
    exact hgt (e.injective (hg1.trans e.map_one.symm))
  have hA := NaturalThreeNormalClassification.alternating_le_nontrivial_normal R hR hn
  have he : e D.cubic∈alternatingGroup (Fin 3) := cube_even _ (by
    rw [←map_pow,hcubic,map_one])
  obtain ⟨n,hnf,hnt⟩ := hA he
  exact ⟨n,hnf,e.injective hnt⟩

end SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates
