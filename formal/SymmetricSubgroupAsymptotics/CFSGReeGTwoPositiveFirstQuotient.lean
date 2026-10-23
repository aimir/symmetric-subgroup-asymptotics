import SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveCentre
import Mathlib.GroupTheory.Commutator.Basic

/-! Literal first-coordinate quotient of the checked positive Ree group.
Its kernel is the actual abelian two-coordinate subgroup a=0. The
statements concern this U3 group, not the derived group of its ambient
fixed group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveFirstQuotient
open CFSGReeGTwoFieldParameters CFSGReeGTwoOriginalPositiveSubgroup
open CFSGReeGTwoPositiveCoordinates
open scoped commutatorElement

def coordinates (m : ℕ) (u : fixedPositiveGroup m) : Fin 3 → Field m :=
  (fixedPositiveEquiv m).symm u

@[simp] theorem coordinates_chart (m : ℕ) (x : Fin 3 → Field m) :
    coordinates m (fixedPositiveChart m x)=x := (fixedPositiveEquiv m).symm_apply_apply x

theorem chart_coordinates (m : ℕ) (u : fixedPositiveGroup m) :
    fixedPositiveChart m (coordinates m u)=u := (fixedPositiveEquiv m).apply_symm_apply u

theorem coordinates_one (m : ℕ) : coordinates m 1=0 := by
  rw [←chart_zero]
  exact coordinates_chart m 0

theorem coordinates_mul (m : ℕ) (u v : fixedPositiveGroup m) :
    coordinates m (u*v)=productCoordinates m (coordinates m u) (coordinates m v) := by
  obtain ⟨x,rfl⟩ := fixedPositiveChart_surjective m u
  obtain ⟨y,rfl⟩ := fixedPositiveChart_surjective m v
  rw [chart_mul,coordinates_chart,coordinates_chart,coordinates_chart]

def firstHom (m : ℕ) : fixedPositiveGroup m →* Multiplicative (Field m) where
  toFun u := Multiplicative.ofAdd (coordinates m u 0)
  map_one' := by change Multiplicative.ofAdd (coordinates m 1 0)=1; rw [coordinates_one]; rfl
  map_mul' u v := by
    change Multiplicative.ofAdd (coordinates m (u*v) 0)=
      Multiplicative.ofAdd (coordinates m u 0+coordinates m v 0)
    rw [coordinates_mul]
    rfl

def firstKernel (m : ℕ) : Subgroup (fixedPositiveGroup m) := (firstHom m).ker

theorem mem_firstKernel_iff (m : ℕ) (u : fixedPositiveGroup m) :
    u∈firstKernel m ↔ coordinates m u 0=0 := Iff.rfl

@[simp] theorem chart_mem_firstKernel_iff (m : ℕ) (x : Fin 3 → Field m) :
    fixedPositiveChart m x∈firstKernel m ↔ x 0=0 := by
  rw [mem_firstKernel_iff,coordinates_chart]

theorem commutator_le_firstKernel (m : ℕ) : commutator (fixedPositiveGroup m)≤firstKernel m := by
  rw [commutator_def]
  apply Subgroup.commutator_le.mpr
  intro u _ v _
  change firstHom m ⁅u,v⁆=1
  rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm _ _

theorem firstKernel_commute (m : ℕ) (u v : fixedPositiveGroup m)
    (hu : u∈firstKernel m) (hv : v∈firstKernel m) : Commute u v := by
  obtain ⟨x,rfl⟩ := fixedPositiveChart_surjective m u
  obtain ⟨y,rfl⟩ := fixedPositiveChart_surjective m v
  have hx := (chart_mem_firstKernel_iff m x).mp hu
  have hy := (chart_mem_firstKernel_iff m y).mp hv
  apply (chart_commute_iff m x y).mpr
  funext i
  fin_cases i <;> simp [productCoordinates,hx,hy,add_comm]

def middleHom (m : ℕ) : firstKernel m →* Multiplicative (Field m) where
  toFun u := Multiplicative.ofAdd (coordinates m u.val 1)
  map_one' := by
    change Multiplicative.ofAdd (coordinates m 1 1)=1
    rw [coordinates_one]
    rfl
  map_mul' u v := by
    have hv := (mem_firstKernel_iff m v.val).mp v.property
    change Multiplicative.ofAdd (coordinates m (u.val*v.val) 1)=
      Multiplicative.ofAdd (coordinates m u.val 1+coordinates m v.val 1)
    rw [coordinates_mul]
    simp [productCoordinates,hv]

theorem middleHom_surjective (m : ℕ) : Function.Surjective (middleHom m) := by
  intro c
  refine ⟨⟨fixedPositiveChart m ![0,c.toAdd,0],(chart_mem_firstKernel_iff m _).mpr rfl⟩,?_⟩
  change Multiplicative.ofAdd (coordinates m (fixedPositiveChart m ![0,c.toAdd,0]) 1)=c
  rw [coordinates_chart]
  rfl

end SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveFirstQuotient
