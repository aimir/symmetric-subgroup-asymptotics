import SymmetricSubgroupAsymptotics.FiniteCayleyGroup

/-!
# Homomorphisms checked only on original-generator transitions

A map of a finite row group is a homomorphism once its identity value and
right-generator transitions are checked. Binary characters can therefore
use linear-sized row tables, without checking every pair of group elements
or enumerating a second graph group.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.EncodedCayleyCertificate

variable {G H ι Code : Type*} [Group G] [Group H] {generators : ι → G}
    {E : GeneratorEncoding generators Code} {n : ℕ}
    (C : EncodedCayleyCertificate E n)
    (values : Fin n → H) (images : ι → H)
    (hstep : ∀ i j, values (C.next i j) = values i * images j)

include hstep

/-- Local generator equations imply the equation for every group word. -/
theorem values_walk (i : Fin n) (w : List ι) :
    values (C.walk i w) = values i * (w.map images).prod := by
  induction w generalizing i with
  | nil => simp [walk]
  | cons j w ih =>
    change values (C.walk (C.next i j) w) = _
    rw [ih, hstep]
    simp only [List.map_cons, List.prod_cons, mul_assoc]

theorem values_word (hidentity : values C.identity = 1) (i : Fin n) :
    values i = ((C.words i).map images).prod := by
  by_cases hi : i = C.identity
  · subst i
    simp only [hidentity, C.words_identity, List.map_nil, List.prod_nil]
  · rw [C.words_parent i hi, List.map_append, List.prod_append,
      List.map_singleton, List.prod_singleton,
      ← values_word hidentity (C.parent i hi), ← hstep, C.parent_next]
termination_by C.rank i
decreasing_by exact C.parent_lt i hi

/-- A transition-checked finite map is an actual group homomorphism. -/
def checkedHom (hinj : Function.Injective C.rows)
    (prev : Fin n → ι → Fin n) (hprev : ∀ i j, C.next (prev i j) j = i)
    (hidentity : values C.identity = 1) :
    letI := C.rowGroup hinj prev hprev
    FiniteGroupRow n →* H := by
  letI := C.rowGroup hinj prev hprev
  exact { toFun := fun i => values i.index
          map_one' := hidentity
          map_mul' := fun i j => by
            change values (C.walk i.index (C.words j.index)) = _
            rw [C.values_walk values images hstep, ← C.values_word values images hstep hidentity j.index] }

@[simp] theorem checkedHom_apply (hinj : Function.Injective C.rows)
    (prev : Fin n → ι → Fin n) (hprev : ∀ i j, C.next (prev i j) j = i)
    (hidentity : values C.identity = 1) (i : FiniteGroupRow n) :
    C.checkedHom values images hstep hinj prev hprev hidentity i = values i.index := rfl

/-- The checked finite map is installed on the original literal subgroup. -/
def checkedOriginalHom [Finite G] (hinj : Function.Injective C.rows)
    (prev : Fin n → ι → Fin n) (hprev : ∀ i j, C.next (prev i j) j = i)
    (hidentity : values C.identity = 1) :
    Subgroup.closure (Set.range generators) →* H := by
  letI := C.rowGroup hinj prev hprev
  exact (C.checkedHom values images hstep hinj prev hprev hidentity).comp
    (C.rowEquiv hinj prev hprev).symm.toMonoidHom

/-- Kernel membership is exactly the checked finite value on the original row. -/
theorem checkedOriginalHom_kernel_iff [Finite G] (hinj : Function.Injective C.rows)
    (prev : Fin n → ι → Fin n) (hprev : ∀ i j, C.next (prev i j) j = i)
    (hidentity : values C.identity = 1) (i : FiniteGroupRow n) :
    C.rowEquiv hinj prev hprev i ∈
      (C.checkedOriginalHom values images hstep hinj prev hprev hidentity).ker ↔
      values i.index = 1 := by
  letI := C.rowGroup hinj prev hprev
  simp only [MonoidHom.mem_ker, checkedOriginalHom, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, checkedHom_apply]

end SymmetricSubgroupAsymptotics.EncodedCayleyCertificate
