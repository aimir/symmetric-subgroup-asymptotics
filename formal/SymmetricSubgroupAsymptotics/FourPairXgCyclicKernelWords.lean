import SymmetricSubgroupAsymptotics.CyclicNormalSubgroupFromConjugates
import SymmetricSubgroupAsymptotics.FiniteGeneratorNormality
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords

/-! Literal eight-point Xg kernel words from the fixed four-block models.
The four conjugates of the first translation span all four binary kernel
coordinates. This is a finite word identity, not a whole-socle assumption. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace FourPairXgCyclicKernelWords

private def first : Equiv.Perm (Fin 8) where
  toFun x := (#[1,0,3,2,4,5,6,7] : Array (Fin 8))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def second : Equiv.Perm (Fin 8) where
  toFun x := (#[2,3,0,1,4,5,6,7] : Array (Fin 8))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def third : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,2,3,5,4,7,6] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def fourth : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,2,3,6,7,4,5] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def a : Equiv.Perm (Fin 8) where
  toFun x := (#[1,2,0,3,5,6,4,7] : Array (Fin 8))[x.val]!
  invFun x := (#[2,0,1,3,6,4,5,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def b : Equiv.Perm (Fin 8) where
  toFun x := (#[5,4,6,7,1,0,2,3] : Array (Fin 8))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def basis : Fin 4 → Equiv.Perm (Fin 8) := ![first, second, third, fourth]
def conjugators : Fin 4 → Equiv.Perm (Fin 8) := ![1, a, b, a*b]

def words : BinaryNormalGeneratorWords basis
    (fun j => conjugators j * basis 0 * (conjugators j)⁻¹) where
  words := ![[0], [0,1], [2], [2,3]]
  equations := by decide +kernel


/-- The exact fixed target from the historical four-block certificate. -/
def generators : Fin 6 → Equiv.Perm (Fin 8) :=
  ![basis 0, basis 1, basis 2, basis 3, a, b]
abbrev Source := Subgroup.closure (Set.range generators)
def sourceGenerators : Fin 6 → Source := closureGenerators generators
def sourceBasis : Fin 4 → Source := fun i => sourceGenerators ⟨i.val, by omega⟩
def sourceConjugators : Fin 4 → Source :=
  ![1, sourceGenerators 4, sourceGenerators 5, sourceGenerators 4 * sourceGenerators 5]
def kernel : Subgroup Source := Subgroup.closure (Set.range sourceBasis)

def conjugationWords (i : Fin 6) (j : Fin 4) : List (Fin 4) :=
  if i < 4 then [j]
  else if i = 4 then ![[0,1], [0], [2,3], [2]] j
  else ![[2], [2,3], [0], [0,1]] j

private theorem conjugation_point_checked : ∀ (i : Fin 6) (j : Fin 4) (x : Fin 8),
    ((((conjugationWords i j).map sourceBasis).prod : Source) :
      Equiv.Perm (Fin 8)) x =
    ((sourceGenerators i * sourceBasis j * (sourceGenerators i)⁻¹ : Source) :
      Equiv.Perm (Fin 8)) x := by
  decide +kernel

instance kernel_normal : kernel.Normal := by
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  rw [← closureGenerators_full generators]
  apply generated_le_normalizer_of_generator_conjugates sourceBasis sourceGenerators
  intro i j
  have he : ((conjugationWords i j).map sourceBasis).prod =
      sourceGenerators i * sourceBasis j * (sourceGenerators i)⁻¹ := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    exact conjugation_point_checked i j x
  rw [← he]
  apply Subgroup.list_prod_mem
  intro y hy
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hy
  exact Subgroup.subset_closure (Set.mem_range_self k)

private theorem cyclic_point_checked : ∀ (i : Fin 4) (x : Fin 8),
    (((((words.words i).map (fun j => sourceConjugators j * sourceBasis 0 *
      (sourceConjugators j)⁻¹)).prod : Source)) : Equiv.Perm (Fin 8)) x =
    (sourceBasis i : Equiv.Perm (Fin 8)) x := by
  decide +kernel

def sourceWords : BinaryNormalGeneratorWords sourceBasis
    (fun j => sourceConjugators j * sourceBasis 0 * (sourceConjugators j)⁻¹) where
  words := words.words
  equations i := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    exact cyclic_point_checked i x

/-- The literal whole binary kernel is cyclic as a normal subgroup of
this actual Xg group, not merely bounded by two normal generators. -/
theorem kernel_cyclic :
    Subgroup.normalClosure (Set.range (fun _ : Fin 1 => sourceBasis 0)) = kernel :=
  normalClosure_single_eq_of_conjugate_words kernel sourceBasis rfl
    (sourceBasis 0) (Subgroup.subset_closure (Set.mem_range_self 0))
    sourceConjugators sourceWords

end FourPairXgCyclicKernelWords
end SymmetricSubgroupAsymptotics
