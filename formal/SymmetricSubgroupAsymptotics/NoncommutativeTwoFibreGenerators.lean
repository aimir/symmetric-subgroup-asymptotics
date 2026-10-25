import SymmetricSubgroupAsymptotics.External.CFSG.Models.MatrixData
import Mathlib.GroupTheory.Subgroup.Centralizer

/-! A noncommutative closure contained in two fibres of an injective map
must occupy both fibres. The occupied elements are genuine original
ambient elements, and they generate exactly the same subgroup. For pinned
matrix models this supplies actual unit generators without assuming that
the raw arrays are invertible or importing an external data audit. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.NoncommutativeTwoFibreGenerators

variable {G A : Type*} [Group G]

theorem exists_left_fibre (s : Set G) (f : G → A) (hf : Function.Injective f)
    (a b : A) (hs : ∀ g ∈ s, f g = a ∨ f g = b)
    (hn : ¬ IsMulCommutative (Subgroup.closure s)) : ∃ x ∈ s, f x = a := by
  by_contra h
  apply hn
  apply Subgroup.isMulCommutative_closure
  intro x hx y hy
  have hxa : f x ≠ a := fun he => h ⟨x,hx,he⟩
  have hya : f y ≠ a := fun he => h ⟨y,hy,he⟩
  have hxy : x = y := hf (((hs x hx).resolve_left hxa).trans
    ((hs y hy).resolve_left hya).symm)
  rw [hxy]

theorem exists_right_fibre (s : Set G) (f : G → A) (hf : Function.Injective f)
    (a b : A) (hs : ∀ g ∈ s, f g = a ∨ f g = b)
    (hn : ¬ IsMulCommutative (Subgroup.closure s)) : ∃ y ∈ s, f y = b :=
  exists_left_fibre s f hf b a (fun g hg => (hs g hg).symm) hn

theorem exists_pair (s : Set G) (f : G → A) (hf : Function.Injective f)
    (a b : A) (hs : ∀ g ∈ s, f g = a ∨ f g = b)
    (hn : ¬ IsMulCommutative (Subgroup.closure s)) :
    ∃ x ∈ s, ∃ y ∈ s, f x = a ∧ f y = b ∧
      Subgroup.closure ({x,y} : Set G) = Subgroup.closure s := by
  obtain ⟨x,hx,hxa⟩ := exists_left_fibre s f hf a b hs hn
  obtain ⟨y,hy,hyb⟩ := exists_right_fibre s f hf a b hs hn
  refine ⟨x,hx,y,hy,hxa,hyb,?_⟩
  congr 1
  apply Set.Subset.antisymm
  · intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hzy
    · exact hx
    · rcases Set.mem_singleton_iff.mp hzy with rfl
      exact hy
  · intro z hz
    rcases hs z hz with ha | hb
    · exact Set.mem_insert_iff.mpr (Or.inl (hf (ha.trans hxa.symm)))
    · exact Set.mem_insert_of_mem _ (Set.mem_singleton_iff.mpr (hf (hb.trans hyb.symm)))

theorem matrix_model_generators (p n : ℕ) (a b : Array String)
    (hn : ¬ IsMulCommutative (CFSG.Models.MatrixData.Model p n a b)) :
    ∃ x ∈ CFSG.Models.MatrixData.generators p n a b,
      ∃ y ∈ CFSG.Models.MatrixData.generators p n a b,
        (x : Matrix (Fin n) (Fin n) (ZMod p)) = CFSG.Models.MatrixData.matrix p n a ∧
        (y : Matrix (Fin n) (Fin n) (ZMod p)) = CFSG.Models.MatrixData.matrix p n b ∧
        Subgroup.closure ({x,y} : Set (Matrix.GeneralLinearGroup (Fin n) (ZMod p))) =
          Subgroup.closure (CFSG.Models.MatrixData.generators p n a b) := by
  exact exists_pair (CFSG.Models.MatrixData.generators p n a b)
    (fun g : Matrix.GeneralLinearGroup (Fin n) (ZMod p) =>
      (g : Matrix (Fin n) (Fin n) (ZMod p)))
    (fun _ _ h => Units.ext h) _ _ (fun _ h => h) hn

end SymmetricSubgroupAsymptotics.NoncommutativeTwoFibreGenerators
