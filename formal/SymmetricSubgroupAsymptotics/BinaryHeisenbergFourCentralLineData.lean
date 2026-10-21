import SymmetricSubgroupAsymptotics.BinaryHeisenbergFourCentralModel

/-! Three actual central line subgroups and reversible original coordinate
predicates. Numerical centre counts are checked independently in small fibres. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical commutatorElement
namespace SymmetricSubgroupAsymptotics.BinaryHeisenbergFourCentralLines
open BinaryHeisenbergFourCentralModel

theorem model_eq {g h : Model} (he : CoordinateEq g h) : g = h := by
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    exact Subtype.ext (funext he.1)
  · exact Subtype.ext (Equiv.ext he.2)

theorem coordinateEq_of_eq {g h : Model} (he : g = h) : CoordinateEq g h :=
  ⟨fun x => congrArg (fun g : Model => g.left.toAdd.val x) he,
    fun x => congrArg (fun g : Model => g.right.val x) he⟩

def direction : Fin 3 → (Fin 2 → ZMod 2) := ![![1,0], ![0,1], ![1,1]]

def lineElement (l : Fin 3) (j : Fin 2) : Model :=
  centralRow (fun x => if j = 0 then 0 else direction l x)

def lineTable (l : Fin 3) : FiniteGeneratedKernelTable (I := Fin 2) generators where
  element := lineElement l
  element_injective := by
    have hc : ∀ (l : Fin 3) (i j : Fin 2),
        CoordinateEq (lineElement l i) (lineElement l j) → i = j := by decide +kernel
    exact fun i j h => hc l i j (coordinateEq_of_eq h)
  identity := 0
  identity_eq := by
    have hc : ∀ l : Fin 3, CoordinateEq (lineElement l 0) 1 := by decide +kernel
    exact model_eq (hc l)
  multiply i j := i + j
  multiply_eq := by
    have hc : ∀ (l : Fin 3) (i j : Fin 2),
        CoordinateEq (lineElement l (i + j)) (lineElement l i * lineElement l j) := by
      decide +kernel
    exact fun i j => model_eq (hc l i j)
  inverse i := i
  inverse_eq := by
    have hc : ∀ (l : Fin 3) (i : Fin 2),
        CoordinateEq (lineElement l i) (lineElement l i)⁻¹ := by decide +kernel
    exact fun i => model_eq (hc l i)
  conjugate _ := Equiv.refl _
  conjugate_eq := by
    have hc : ∀ (l : Fin 3) (j : GeneratorIndex) (i : Fin 2),
        CoordinateEq (lineElement l i) (generators j * lineElement l i * (generators j)⁻¹) := by
      decide +kernel
    exact fun j i => model_eq (hc l j i)

abbrev line (l : Fin 3) := (lineTable l).subgroup
instance (l : Fin 3) : (line l).Normal := (lineTable l).normal generators_full

theorem line_card (l : Fin 3) : Nat.card (line l) = 2 := by
  rw [← Nat.card_congr (lineTable l).chartEquiv, Nat.card_fin]

theorem central_line_cases (L : Subgroup Model) (hL : L ≤ D) (hcard : Nat.card L = 2) :
    ∃ l : Fin 3, L = line l := by
  haveI : Nontrivial L := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; decide)
  obtain ⟨x, hx⟩ := exists_ne (1 : L)
  obtain ⟨a, ha⟩ := hL x.property
  have hc : ∀ a : Fin 2 → ZMod 2,
      CoordinateEq (centralRow a) 1 ∨
        ∃ l : Fin 3, CoordinateEq (centralRow a) (lineElement l 1) := by decide +kernel
  rcases hc a with hzero | ⟨l, hl⟩
  · apply False.elim
    apply hx
    apply Subtype.ext
    exact ha.symm.trans (model_eq hzero)
  · refine ⟨l, ?_⟩
    have hxl : (x : Model) = lineElement l 1 := ha.symm.trans (model_eq hl)
    have hle : line l ≤ L := by
      rintro y ⟨j, rfl⟩
      change lineElement l j ∈ L
      fin_cases j
      · change lineElement l 0 ∈ L
        have he : lineElement l 0 = 1 := (lineTable l).identity_eq
        rw [he]
        exact L.one_mem
      · change lineElement l 1 ∈ L
        rw [← hxl]
        exact x.property
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [line_card, hcard])).symm

def centerMask (a : KernelIndex × Fin 32) : Prop :=
  ∀ j : GeneratorIndex, CoordinateEq ⁅row a, generators j⁆ 1

instance (a : KernelIndex × Fin 32) : Decidable (centerMask a) :=
  inferInstanceAs (Decidable (∀ j : GeneratorIndex, CoordinateEq ⁅row a, generators j⁆ 1))

def lineCenterMask (l : Fin 3) (a : KernelIndex × Fin 32) : Prop :=
  ∀ j : GeneratorIndex, ∃ k : Fin 2,
    CoordinateEq (lineElement l k) ⁅row a, generators j⁆

instance (l : Fin 3) (a : KernelIndex × Fin 32) : Decidable (lineCenterMask l a) :=
  inferInstanceAs (Decidable (∀ j : GeneratorIndex, ∃ k : Fin 2,
    CoordinateEq (lineElement l k) ⁅row a, generators j⁆))

end SymmetricSubgroupAsymptotics.BinaryHeisenbergFourCentralLines
