import SymmetricSubgroupAsymptotics.FiniteCayleyReflection
import Mathlib.Tactic.DeriveFintype

/-!
# Executable finite row groups from reflected Cayley certificates

Only generator transitions are checked. Arbitrary multiplication follows a
certified word through that table; inverse multiplication uses checked
inverse transitions. Faithfulness proves all group axioms and identifies
this executable finite group with the literal original generated subgroup.
No quadratic multiplication table or cubic associativity test is required.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
/-- A row index with no unrelated arithmetic group operations. -/
@[ext]
structure FiniteGroupRow (n : ℕ) where
  index : Fin n
  deriving DecidableEq, Fintype

namespace EncodedCayleyCertificate

variable {G ι Code : Type*} [Group G] {generators : ι → G}
    {E : GeneratorEncoding generators Code} {n : ℕ}
    (C : EncodedCayleyCertificate E n)

/-- Follow right-generator edges starting at an arbitrary row. -/
def walk (i : Fin n) (w : List ι) : Fin n := w.foldl C.next i

theorem elements_walk (i : Fin n) (w : List ι) :
    C.toCayley.elements (C.walk i w) =
      C.toCayley.elements i * (w.map generators).prod := by
  induction w generalizing i with
  | nil => simp [walk]
  | cons j w ih =>
    change C.toCayley.elements (C.walk (C.next i j) w) = _
    rw [ih]
    change C.toCayley.elements (C.toCayley.next i j) * _ = _
    rw [C.toCayley.next_eq]
    simp only [List.map_cons, List.prod_cons, mul_assoc]

/-- Computable multiplication on row indices. -/
def rowMul (i j : Fin n) : Fin n := C.walk i (C.words j)

theorem elements_mul (i j : Fin n) :
    C.toCayley.elements (C.rowMul i j) =
      C.toCayley.elements i * C.toCayley.elements j := C.elements_walk i (C.words j)

/-- Follow the inverse word using supplied inverse-generator transitions. -/
def undo (C : EncodedCayleyCertificate E n) (prev : Fin n → ι → Fin n) (i : Fin n) (w : List ι) : Fin n :=
  w.foldr (fun j r => prev r j) i

theorem elements_prev (prev : Fin n → ι → Fin n)
    (hprev : ∀ i j, C.next (prev i j) j = i) (i : Fin n) (j : ι) :
    C.toCayley.elements (prev i j) = C.toCayley.elements i * (generators j)⁻¹ := by
  have h := C.toCayley.next_eq (prev i j) j
  change C.toCayley.elements (C.next (prev i j) j) = _ at h
  rw [hprev] at h
  exact eq_mul_inv_iff_mul_eq.mpr h.symm

theorem elements_undo (prev : Fin n → ι → Fin n)
    (hprev : ∀ i j, C.next (prev i j) j = i) (i : Fin n) (w : List ι) :
    C.toCayley.elements (C.undo prev i w) =
      C.toCayley.elements i * ((w.map generators).prod)⁻¹ := by
  induction w with
  | nil => simp [undo]
  | cons j w ih =>
    change C.toCayley.elements (prev (C.undo prev i w) j) = _
    rw [C.elements_prev prev hprev, ih]
    simp only [List.map_cons, List.prod_cons, mul_inv_rev, mul_assoc]

def rowInv (prev : Fin n → ι → Fin n) (i : Fin n) : Fin n :=
  C.undo prev C.identity (C.words i)

theorem elements_inv (prev : Fin n → ι → Fin n)
    (hprev : ∀ i j, C.next (prev i j) j = i) (i : Fin n) :
    C.toCayley.elements (C.rowInv prev i) = (C.toCayley.elements i)⁻¹ := by
  rw [rowInv, C.elements_undo prev hprev]
  change C.toCayley.elements C.toCayley.identity * _ = _
  rw [C.toCayley.identity_eq, one_mul]
  rfl

theorem elements_injective (hinj : Function.Injective C.rows) :
    Function.Injective C.toCayley.elements := by
  intro i j he
  apply hinj
  simpa only [C.encode_elements] using congrArg E.encode he

/-- The finite row operations satisfy the group laws because their map to
the actual original group is faithful. The operations themselves remain
executable table walks. -/
@[reducible]
def rowGroup (hinj : Function.Injective C.rows)
    (prev : Fin n → ι → Fin n) (hprev : ∀ i j, C.next (prev i j) j = i) :
    Group (FiniteGroupRow n) where
  mul i j := ⟨C.rowMul i.index j.index⟩
  one := ⟨C.identity⟩
  inv i := ⟨C.rowInv prev i.index⟩
  mul_assoc := by
    intro i j k
    apply FiniteGroupRow.ext
    apply C.elements_injective hinj
    change C.toCayley.elements (C.rowMul (C.rowMul i.index j.index) k.index) =
      C.toCayley.elements (C.rowMul i.index (C.rowMul j.index k.index))
    simp only [C.elements_mul, mul_assoc]
  one_mul := by
    intro i
    apply FiniteGroupRow.ext
    apply C.elements_injective hinj
    change C.toCayley.elements (C.rowMul C.toCayley.identity i.index) = _
    simp only [C.elements_mul, C.toCayley.identity_eq, one_mul]
  mul_one := by
    intro i
    apply FiniteGroupRow.ext
    apply C.elements_injective hinj
    change C.toCayley.elements (C.rowMul i.index C.toCayley.identity) = _
    simp only [C.elements_mul, C.toCayley.identity_eq, mul_one]
  inv_mul_cancel := by
    intro i
    apply FiniteGroupRow.ext
    apply C.elements_injective hinj
    change C.toCayley.elements (C.rowMul (C.rowInv prev i.index) i.index) =
      C.toCayley.elements C.toCayley.identity
    simp only [C.elements_mul, C.elements_inv prev hprev, inv_mul_cancel,
      C.toCayley.identity_eq]

/-- The actual permutation/group action of the executable finite row group. -/
def rowHom (hinj : Function.Injective C.rows)
    (prev : Fin n → ι → Fin n) (hprev : ∀ i j, C.next (prev i j) j = i) :
    letI := C.rowGroup hinj prev hprev
    FiniteGroupRow n →* G := by
  letI := C.rowGroup hinj prev hprev
  exact { toFun := fun i => C.toCayley.elements i.index
          map_one' := C.toCayley.identity_eq
          map_mul' := fun i j => C.elements_mul i.index j.index }

theorem rowHom_injective (hinj : Function.Injective C.rows)
    (prev : Fin n → ι → Fin n) (hprev : ∀ i j, C.next (prev i j) j = i) :
    Function.Injective (C.rowHom hinj prev hprev) := by
  intro i j he
  exact FiniteGroupRow.ext (C.elements_injective hinj he)

theorem rowHom_range [Finite G] (hinj : Function.Injective C.rows)
    (prev : Fin n → ι → Fin n) (hprev : ∀ i j, C.next (prev i j) j = i) :
    letI := C.rowGroup hinj prev hprev
    (C.rowHom hinj prev hprev).range = Subgroup.closure (Set.range generators) := by
  letI := C.rowGroup hinj prev hprev
  ext g
  rw [C.toCayley.mem_closure_iff]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨i.index,hi⟩
  · rintro ⟨i,hi⟩
    exact ⟨⟨i⟩,hi⟩

/-- A complete typed equivalence, preserving the original group operation. -/
def rowEquiv [Finite G] (hinj : Function.Injective C.rows)
    (prev : Fin n → ι → Fin n) (hprev : ∀ i j, C.next (prev i j) j = i) :
    letI := C.rowGroup hinj prev hprev
    FiniteGroupRow n ≃* Subgroup.closure (Set.range generators) := by
  letI := C.rowGroup hinj prev hprev
  let f := (C.rowHom hinj prev hprev).codRestrict
    (Subgroup.closure (Set.range generators)) (fun i =>
      (C.toCayley.mem_closure_iff _).mpr ⟨i.index,rfl⟩)
  apply MulEquiv.ofBijective f
  constructor
  · intro i j he
    exact C.rowHom_injective hinj prev hprev (congrArg Subtype.val he)
  · rintro ⟨g,hg⟩
    obtain ⟨i,hi⟩ := (C.toCayley.mem_closure_iff g).mp hg
    exact ⟨⟨i⟩,Subtype.ext hi⟩

end EncodedCayleyCertificate
end SymmetricSubgroupAsymptotics
