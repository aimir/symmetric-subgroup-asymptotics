import SymmetricSubgroupAsymptotics.Non2PreE7AffineModel
import SymmetricSubgroupAsymptotics.FiniteThreeNormalChainSocleGenerators

/-!
# The normal chain of an irreducible affine group with simple complement

Every nontrivial normal subgroup contains the translations. The projection
to a simple linear complement then leaves exactly the translation subgroup
and the full affine group. A specified nonzero vector supplies the literal
middle-state generator for the quotient-socle interface.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace AffineModel

open SemidirectProduct

variable {p d : ℕ} [Fact p.Prime]
variable (R : Subgroup (GLV p d))

/-- A nonzero translation remains nonidentity in the affine group. -/
theorem inl_ofAdd_ne_one {v : V p d} (hv : v ≠ 0) :
    (inl (Multiplicative.ofAdd v) : Aff R) ≠ 1 := by
  intro h
  apply hv
  have h' : Multiplicative.ofAdd v = (1 : Multiplicative (V p d)) :=
    inl_injective (h.trans (map_one inl).symm)
  exact congrArg Multiplicative.toAdd h'

/-- A nonzero vector witnesses that the translation subgroup is nontrivial. -/
theorem Vsub_ne_bot_of_nonzero {v : V p d} (hv : v ≠ 0) : Vsub R ≠ ⊥ := by
  intro h
  apply inl_ofAdd_ne_one R hv
  apply Subgroup.mem_bot.mp
  rw [← h]
  exact ⟨Multiplicative.ofAdd v, rfl⟩

/-- A nontrivial linear complement makes the translation subgroup proper. -/
theorem Vsub_ne_top_of_nontrivial [Nontrivial R] : Vsub R ≠ ⊤ := by
  obtain ⟨r, hr⟩ := exists_ne (1 : R)
  intro h
  apply hr
  have hm : (inr r : Aff R) ∈ Vsub R := by
    rw [h]
    exact Subgroup.mem_top _
  exact (mem_Vsub R _).mp hm

/-- Projection to a simple linear complement classifies the normal subgroups. -/
theorem normal_eq_bot_or_Vsub_or_top [IsSimpleGroup R]
    (hirr : Irreducible R) (N : Subgroup (Aff R)) (hN : N.Normal) :
    N = ⊥ ∨ N = Vsub R ∨ N = ⊤ := by
  by_cases hbot : N = ⊥
  · exact Or.inl hbot
  right
  letI : N.Normal := hN
  let π : Aff R →* R := rightHom
  have hker : π.ker ≤ N := by
    rw [← range_inl_eq_ker_rightHom]
    exact Vsub_le_normal hirr N hbot
  have hmap : (N.map π).Normal := hN.map π rightHom_surjective
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map π) hmap with hm | hm
  · left
    calc
      N = (N.map π).comap π := (Subgroup.comap_map_eq_self hker).symm
      _ = π.ker := by rw [hm]; rfl
      _ = Vsub R := range_inl_eq_ker_rightHom.symm
  · right
    calc
      N = (N.map π).comap π := (Subgroup.comap_map_eq_self hker).symm
      _ = ⊤ := by rw [hm, Subgroup.comap_top]

/-- A faithful irreducible affine action with simple linear complement has
the checked three-state normal chain, generated in the middle by any nonzero
translation. -/
def simpleComplementNormalChain [IsSimpleGroup R]
    (hirr : Irreducible R) (v : V p d) (hv : v ≠ 0) :
    FiniteThreeNormalChainData (Aff R) where
  middle := Vsub R
  middle_normal := inferInstance
  middle_ne_bot := Vsub_ne_bot_of_nonzero R hv
  middle_ne_top := Vsub_ne_top_of_nontrivial R
  normal_eq_bot_or_middle_or_top := normal_eq_bot_or_Vsub_or_top R hirr
  generator := inl (Multiplicative.ofAdd v)
  generator_mem := ⟨Multiplicative.ofAdd v, rfl⟩
  generator_ne_one := inl_ofAdd_ne_one R hv

/-- Every normal quotient has a padded two-position socle witness. -/
def quotientSocleGeneratorBound_two_of_simpleComplement [IsSimpleGroup R]
    (hirr : Irreducible R) (v : V p d) (hv : v ≠ 0)
    (N : {N : Subgroup (Aff R) // N.Normal}) :
    SocleNormalGeneratorBound (Aff R ⧸ N.1) 2 :=
  (simpleComplementNormalChain R hirr v hv).quotientSocleGeneratorBound_two N

end AffineModel
end SymmetricSubgroupAsymptotics

end
