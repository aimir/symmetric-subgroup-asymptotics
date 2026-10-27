import SymmetricSubgroupAsymptotics.External.CFSG.Models.Presentations.J2
import Mathlib.GroupTheory.Subgroup.Simple

/-! The exact original five-relator J2 presentation maps equivalently to any
actual nontrivial generating pair satisfying those five equations, under
inherited simplicity of the ORIGINAL presentation. No target simplicity,
finite-cardinality, named-model recognition or order certificate is used.
The two extra identities for a concrete native pair remain real obligations. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.JankoTwoStandardPairPresentationEquivalence

variable {G : Type*} [Group G]

def lastRelator (a b : G) : G :=
  ((((((((((((((((((((((((a * b) * a) * b) * a) * ((b⁻¹) ^ 1)) * a) * b) * a) * ((b⁻¹) ^ 1)) * a) * ((b⁻¹) ^ 1)) * a) * b) * a) * b) * a) * ((b⁻¹) ^ 1)) * a) * ((b⁻¹) ^ 1)) * a) * b) * a) * ((b⁻¹) ^ 1)) ^ 3)

def generators (a b : G) : Fin 2 → G := fun i => if i = 0 then a else b

@[simp] theorem generators_zero (a b : G) : generators a b 0 = a := rfl
@[simp] theorem generators_one (a b : G) : generators a b 1 = b := rfl

variable (a b : G) (ha : a ^ 2 = 1) (hb : b ^ 3 = 1)
  (hab : (a * b) ^ 7 = 1) (hc : CFSG.Models.commWord a b ^ 12 = 1)
  (hlast : lastRelator a b = 1)

include ha hb hab hc hlast in
theorem all_relators : ∀ r ∈ CFSG.Models.Presentations.J2.relators,
    FreeGroup.lift (generators a b) r = 1 := by
  intro r hr
  simp only [CFSG.Models.Presentations.J2.relators,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa only [map_pow,FreeGroup.lift_apply_of,generators_zero] using ha
  · simpa only [map_pow,FreeGroup.lift_apply_of,generators_one] using hb
  · simpa only [map_pow,map_mul,FreeGroup.lift_apply_of,generators_zero,generators_one] using hab
  · simpa only [CFSG.Models.commWord,map_pow,map_mul,map_inv,FreeGroup.lift_apply_of,
      generators_zero,generators_one] using hc
  · simpa only [lastRelator,map_pow,map_mul,map_inv,FreeGroup.lift_apply_of,
      generators_zero,generators_one] using hlast

def representation : CFSG.Models.Presentations.J2.Model →* G :=
  PresentedGroup.toGroup (all_relators a b ha hb hab hc hlast)

theorem representation_of_zero :
    representation a b ha hb hab hc hlast (PresentedGroup.of (0 : Fin 2)) = a := by
  simp [representation,generators]

theorem representation_of_one :
    representation a b ha hb hab hc hlast (PresentedGroup.of (1 : Fin 2)) = b := by
  simp [representation,generators]

theorem representation_surjective (hgen : Subgroup.closure ({a,b} : Set G) = ⊤) :
    Function.Surjective (representation a b ha hb hab hc hlast) := by
  let f := representation a b ha hb hab hc hlast
  have hcl : Subgroup.closure ({a,b} : Set G) ≤ f.range := by
    apply (Subgroup.closure_le f.range).mpr
    have haRange : a ∈ f.range :=
      ⟨PresentedGroup.of (0 : Fin 2),representation_of_zero a b ha hb hab hc hlast⟩
    have hbRange : b ∈ f.range :=
      ⟨PresentedGroup.of (1 : Fin 2),representation_of_one a b ha hb hab hc hlast⟩
    exact Set.insert_subset_iff.mpr ⟨haRange,Set.singleton_subset_iff.mpr hbRange⟩
  rw [hgen] at hcl
  intro g
  exact hcl (show g ∈ (⊤ : Subgroup G) from trivial)

theorem representation_injective [IsSimpleGroup CFSG.Models.Presentations.J2.Model]
    (hne : a ≠ 1) : Function.Injective (representation a b ha hb hab hc hlast) := by
  let f := representation a b ha hb hab hc hlast
  rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with hbot | htop
  · exact f.ker_eq_bot_iff.mp hbot
  · have hm : PresentedGroup.of (0 : Fin 2) ∈ f.ker := by rw [htop]; trivial
    have he : f (PresentedGroup.of (0 : Fin 2)) = 1 := hm
    exact (hne ((representation_of_zero a b ha hb hab hc hlast).symm.trans he)).elim

def equiv [IsSimpleGroup CFSG.Models.Presentations.J2.Model]
    (hne : a ≠ 1) (hgen : Subgroup.closure ({a,b} : Set G) = ⊤) :
    CFSG.Models.Presentations.J2.Model ≃* G :=
  MulEquiv.ofBijective (representation a b ha hb hab hc hlast)
    ⟨representation_injective a b ha hb hab hc hlast hne,
      representation_surjective a b ha hb hab hc hlast hgen⟩

end SymmetricSubgroupAsymptotics.JankoTwoStandardPairPresentationEquivalence
