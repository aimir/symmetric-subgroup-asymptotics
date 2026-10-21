import SymmetricSubgroupAsymptotics.CFSGTypeASLTwoWeyl
import Mathlib.GroupTheory.Solvable

/-! Literal upper roots and their soluble normalizer in SL₂. Every
matrix condition is imposed on the original determinant-one matrix; the
field and its characteristic remain unchanged. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSLTwoUpperRoots
open Matrix CFSGTypeAElementaryMatrices CFSGTypeASLTwoWeyl
variable {F : Type*} [Field F]

@[simp] theorem upper_entry00 (a : F) : (upper a).val 0 0=1 := by
  simp [upper,elementary,Matrix.transvection]
@[simp] theorem upper_entry01 (a : F) : (upper a).val 0 1=a := by
  simp [upper,elementary,Matrix.transvection]
@[simp] theorem upper_entry10 (a : F) : (upper a).val 1 0=0 := by
  simp [upper,elementary,Matrix.transvection]
@[simp] theorem upper_entry11 (a : F) : (upper a).val 1 1=1 := by
  simp [upper,elementary,Matrix.transvection]

def upperHom : Multiplicative F →* SL2 (F:=F) where
  toFun a := upper a.toAdd
  map_one' := elementary_zero (by decide : (0 : Fin 2)≠1)
  map_mul' a b := elementary_add (by decide : (0 : Fin 2)≠1) a.toAdd b.toAdd

theorem upperHom_injective : Function.Injective (upperHom (F:=F)) := by
  intro a b h
  have he := congrArg (fun g : SL2 (F:=F) => g.val 0 1) h
  change (upper a.toAdd).val 0 1 = (upper b.toAdd).val 0 1 at he
  simp only [upper_entry01] at he
  exact congrArg Multiplicative.ofAdd he

def upperRoot : Subgroup (SL2 (F:=F)) := (upperHom (F:=F)).range

theorem upper_mem (a : F) : upper a∈upperRoot (F:=F) :=
  ⟨Multiplicative.ofAdd a,rfl⟩

theorem eq_upper_of_entries (g : SL2 (F:=F))
    (h00 : g.val 0 0=1) (h10 : g.val 1 0=0) (h11 : g.val 1 1=1) :
    g=upper (g.val 0 1) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp_all

theorem mem_upperRoot_iff (g : SL2 (F:=F)) :
    g∈upperRoot (F:=F) ↔ g.val 0 0=1 ∧ g.val 1 0=0 ∧ g.val 1 1=1 := by
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨upper_entry00 _,upper_entry10 _,upper_entry11 _⟩
  · rintro ⟨h00,h10,h11⟩
    rw [eq_upper_of_entries g h00 h10 h11]
    exact upper_mem _

def borel : Subgroup (SL2 (F:=F)) where
  carrier := {g | g.val 1 0=0}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change a.val 1 0=0 at ha
    change b.val 1 0=0 at hb
    change (a.val*b.val) 1 0=0
    simp only [Matrix.mul_apply,Fin.sum_univ_two,ha,hb,mul_zero,zero_mul,add_zero]
  inv_mem' := by
    intro a ha
    change (a⁻¹).val 1 0=0
    rw [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]
    simpa using neg_eq_zero.mpr ha

theorem borel_det (g : borel (F:=F)) : g.val.val 0 0*g.val.val 1 1=1 := by
  have hd := g.val.property
  rw [Matrix.det_fin_two,g.property,mul_zero,sub_zero] at hd
  exact hd

def diagonal : borel (F:=F) →* Fˣ where
  toFun g := ⟨g.val.val 0 0,g.val.val 1 1,borel_det g,by simpa only [mul_comm] using borel_det g⟩
  map_one' := by apply Units.ext; rfl
  map_mul' a b := by
    apply Units.ext
    have hb : b.val.val 1 0=0 := b.property
    change (a.val.val*b.val.val) 0 0=a.val.val 0 0*b.val.val 0 0
    simp only [Matrix.mul_apply,Fin.sum_univ_two,hb,mul_zero,add_zero]

def upperIntoBorel : Multiplicative F →* borel (F:=F) where
  toFun a := ⟨upperHom a,upper_entry10 _⟩
  map_one' := Subtype.ext (upperHom (F:=F)).map_one
  map_mul' a b := Subtype.ext ((upperHom (F:=F)).map_mul a b)

theorem borel_isSolvable : IsSolvable (borel (F:=F)) := by
  apply solvable_of_ker_le_range (upperIntoBorel (F:=F)) (diagonal (F:=F))
  intro g hg
  have h00 : g.val.val 0 0=1 := congrArg Units.val hg
  have h11 : g.val.val 1 1=1 := by simpa only [h00,one_mul] using borel_det g
  refine ⟨Multiplicative.ofAdd (g.val.val 0 1),?_⟩
  apply Subtype.ext
  exact (eq_upper_of_entries g.val h00 g.property h11).symm

/-- Normalizing all upper roots forces the actual lower-left entry to
vanish. Only the single root with parameter one is needed. -/
theorem normalizer_le_borel :
    Subgroup.normalizer (upperRoot (F:=F) : Set (SL2 (F:=F))) ≤ borel (F:=F) := by
  intro g hg
  have hc : g*upper (1 : F)*g⁻¹∈upperRoot (F:=F) :=
    (Subgroup.mem_normalizer_iff.mp hg _).mp (upper_mem 1)
  obtain ⟨a,ha⟩ := hc
  have hm : g*upper (1 : F)=upper a.toAdd*g := by
    have he := congrArg (fun z : SL2 (F:=F) => z*g) ha
    simpa only [upperHom,mul_assoc,inv_mul_cancel,mul_one] using he.symm
  have he := congrArg (fun z : SL2 (F:=F) => z.val 1 1) hm
  change (g.val*(upper (1 : F)).val) 1 1=((upper a.toAdd).val*g.val) 1 1 at he
  simp only [Matrix.mul_apply,Fin.sum_univ_two,upper_entry01,
    upper_entry10,upper_entry11,mul_one,one_mul,zero_mul,zero_add] at he
  exact add_eq_right.mp he

theorem upperRoot_normalizer_isSolvable :
    IsSolvable (Subgroup.normalizer (upperRoot (F:=F) : Set (SL2 (F:=F)))) := by
  letI : IsSolvable (borel (F:=F)) := borel_isSolvable
  exact solvable_of_solvable_injective (f := Subgroup.inclusion normalizer_le_borel)
    (Subgroup.inclusion_injective _)

end SymmetricSubgroupAsymptotics.CFSGSLTwoUpperRoots
