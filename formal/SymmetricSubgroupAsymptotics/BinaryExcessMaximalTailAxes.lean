import SymmetricSubgroupAsymptotics.MarkedC4RDTOriginalWordStructure

/-! Maximal full product projections force the literal remaining kernel
axes to be proper. This is independent of binary groups, permutation
actions, normal-generator estimates, and any exceptional classification. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryExcessMaximalTailAxes

open MarkedC4.RDTOriginalWordStructure

variable {t : ℕ} (K : Fin t → Type) [∀ i, Group (K i)]
    (L : Subgroup (∀ i, K i)) (tail : Finset (Fin t))

def coordinate (i : Fin t) : L →* K i := (Pi.evalMonoidHom K i).comp L.subtype

def kernelAxis (i : Fin t) : Subgroup (K i) :=
  ((tailProjection K L tail).ker).map (coordinate K L i)

/-- A full kernel axis lets one append that coordinate to an already
full product projection. The adjusting element lives in the actual kernel
of the original tail projection. -/
theorem surjective_insert
    (htail : Function.Surjective (tailProjection K L tail)) (i : Fin t)
    (haxis : kernelAxis K L tail i = ⊤) :
    Function.Surjective (tailProjection K L (insert i tail)) := by
  intro w
  let old : (j : {j // j ∈ tail}) → K j.1 :=
    fun j => w ⟨j.1, Finset.mem_insert_of_mem j.2⟩
  obtain ⟨x, hx⟩ := htail old
  have ha : w ⟨i, Finset.mem_insert_self _ _⟩ * (x.1 i)⁻¹ ∈
      kernelAxis K L tail i := by rw [haxis]; trivial
  obtain ⟨y, hy, hcy⟩ := ha
  have hyTail : tailProjection K L tail y = 1 := MonoidHom.mem_ker.mp hy
  let z : L := y * x
  have hzTail : tailProjection K L tail z = old := by
    change tailProjection K L tail (y * x) = old
    rw [map_mul, hyTail, one_mul, hx]
  have hzi : z.1 i = w ⟨i, Finset.mem_insert_self _ _⟩ := by
    change y.1 i * x.1 i = _
    change y.1 i = w ⟨i, Finset.mem_insert_self _ _⟩ * (x.1 i)⁻¹ at hcy
    rw [hcy, inv_mul_cancel_right]
  refine ⟨z, ?_⟩
  funext j
  by_cases hji : j.1 = i
  · have hj : j = ⟨i, Finset.mem_insert_self _ _⟩ := Subtype.ext hji
    rw [hj]
    exact hzi
  · have hjtail : j.1 ∈ tail := (Finset.mem_insert.mp j.2).resolve_left hji
    have he := congrFun hzTail (⟨j.1, hjtail⟩ : {j // j ∈ tail})
    exact he

/-- Every coordinate outside a maximal full product projection has a
proper literal tail-kernel axis. -/
theorem kernelAxis_ne_top (hmax : MaximalTail K L tail)
    (i : Fin t) (hi : i ∉ tail) : kernelAxis K L tail i ≠ ⊤ := by
  intro haxis
  have hcard := hmax.2 (insert i tail) (surjective_insert K L tail hmax.1 i haxis)
  rw [Finset.card_insert_of_notMem hi] at hcard
  omega

/-- Any actual kernel subimage, including each later normal-filtration
diagonal, inherits the same properness. -/
theorem map_ne_top_of_le_kernel (hmax : MaximalTail K L tail)
    (i : Fin t) (hi : i ∉ tail) (U : Subgroup L)
    (hU : U ≤ (tailProjection K L tail).ker) :
    U.map (coordinate K L i) ≠ ⊤ := by
  intro htop
  apply kernelAxis_ne_top K L tail hmax i hi
  apply top_unique
  rw [← htop]
  exact Subgroup.map_mono hU

end SymmetricSubgroupAsymptotics.BinaryExcessMaximalTailAxes
