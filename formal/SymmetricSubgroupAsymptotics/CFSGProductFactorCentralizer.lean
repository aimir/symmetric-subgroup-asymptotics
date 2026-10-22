import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.GroupTheory.Subgroup.Centralizer

/-! A literal coordinate factor of a direct product is normal, isomorphic
to the factor, and supplemented by its actual centralizer. No decomposition
or representation chart is a hypothesis of these facts. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGProductFactorCentralizer

variable {I S : Type} [Group S]

def factorHom (i : I) : S →* (I → S) :=
  MonoidHom.mulSingle (fun _ : I => S) i

def factor (i : I) : Subgroup (I → S) := (factorHom (S := S) i).range

theorem factorHom_injective (i : I) : Function.Injective (factorHom (S := S) i) := by
  intro a b hab
  simpa only [factorHom, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same]
    using congrFun hab i

def factorEquiv (i : I) : S ≃* factor (S := S) i :=
  MonoidHom.ofInjective (factorHom_injective i)

instance factor_normal (i : I) : (factor (S := S) i).Normal where
  conj_mem := by
    intro n hn g
    obtain ⟨a, rfl⟩ := hn
    refine ⟨g i * a * (g i)⁻¹, ?_⟩
    ext j
    by_cases hji : j = i
    · subst j
      simp [factorHom]
    · simp [factorHom, hji]

theorem mem_centralizer_of_coordinate_one (i : I) (g : I → S) (hg : g i = 1) :
    g ∈ Subgroup.centralizer (factor (S := S) i : Set (I → S)) := by
  apply Subgroup.mem_centralizer_iff.mpr
  intro n hn
  obtain ⟨a, rfl⟩ := hn
  ext j
  by_cases hji : j = i
  · subst j
    simp [factorHom, hg]
  · simp [factorHom, hji]

theorem factor_sup_centralizer_eq_top (i : I) :
    factor (S := S) i ⊔ Subgroup.centralizer (factor (S := S) i : Set (I → S)) = ⊤ := by
  apply top_unique
  intro g _
  let a := factorHom (S := S) i (g i)
  let c := a⁻¹ * g
  have ha : a ∈ factor (S := S) i := ⟨g i, rfl⟩
  have hc0 : c i = 1 := by simp [c, a, factorHom]
  have hc := mem_centralizer_of_coordinate_one i c hc0
  have hm : a * c ∈ factor (S := S) i ⊔
      Subgroup.centralizer (factor (S := S) i : Set (I → S)) :=
    Subgroup.mul_mem _ ((show factor (S := S) i ≤ _ from le_sup_left) ha)
      ((show Subgroup.centralizer (factor (S := S) i : Set (I → S)) ≤ _ from le_sup_right) hc)
  simpa [c] using hm

end SymmetricSubgroupAsymptotics.CFSGProductFactorCentralizer
