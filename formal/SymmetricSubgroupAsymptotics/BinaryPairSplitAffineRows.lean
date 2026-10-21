import SymmetricSubgroupAsymptotics.BinaryPairAffineGeneratorNormalForm
import SymmetricSubgroupAsymptotics.LinearSemidirectCoprimeSocleBounds
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.Algebra.Field.ZMod

/-! The literal zero-offset pair model has reversible coordinates consisting
of its actual correlated kernel vector and original top permutation. This
binds sparse affine-coordinate rows without a multiplication/action table. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {X : Type} {w : ℕ} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U (Fin w))

/-- General affine multiplication in destination coordinates. -/
theorem affinePermutation_mul_formula (t s : Equiv.Perm (Fin w))
    (a b : Fin w → ZMod 2) :
    F.affinePermutation t a * F.affinePermutation s b =
      F.affinePermutation (t * s) (a + (fun i => b (t.symm i))) := by
  apply Equiv.ext
  intro x
  obtain ⟨⟨i, c⟩, rfl⟩ := F.frame.surjective x
  change F.affinePermutation t a (F.affinePermutation s b (F.frame (i, c))) = _
  rw [F.affinePermutation_apply_frame, F.affinePermutation_apply_frame,
    F.affinePermutation_apply_frame]
  apply congrArg F.frame
  apply congrArg (fun z : ZMod 2 => (t (s i), z))
  change c + b (s i) + a (t (s i)) =
    c + (a (t (s i)) + b (t.symm (t (s i))))
  rw [Equiv.symm_apply_apply]
  abel

/-- Literal affine coordinates are injective on the original point set. -/
theorem affinePermutation_coordinates_injective
    {t s : Equiv.Perm (Fin w)} {a b : Fin w → ZMod 2}
    (he : F.affinePermutation t a = F.affinePermutation s b) : t = s ∧ a = b := by
  have hp (i : Fin w) : (t i, a (t i)) = (s i, b (s i)) := by
    have hh := congrArg (fun p : Equiv.Perm X => p (F.frame (i, 0))) he
    change F.affinePermutation t a (F.frame (i, 0)) =
      F.affinePermutation s b (F.frame (i, 0)) at hh
    rw [F.affinePermutation_apply_frame, F.affinePermutation_apply_frame,
      zero_add, zero_add] at hh
    exact F.frame.injective hh
  have ht : t = s := Equiv.ext (fun i => congrArg Prod.fst (hp i))
  refine ⟨ht, ?_⟩
  subst s
  funext j
  have hh := congrArg Prod.snd (hp (t.symm j))
  simpa only [Equiv.apply_symm_apply] using hh

/-- The action is the same original top action on the actual kernel. -/
def splitAffineLinearAction : F.top.range →* (F.kernelSpace ≃ₗ[ZMod 2] F.kernelSpace) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) F.kernelSpace).toMonoidHom.comp
    F.kernelTopPermutationSubrepresentation.toRepresentation.asGroupHom

abbrev SplitAffineModel := LinearSemidirectCoprimeSocleBounds.Model F.splitAffineLinearAction

/-- The reversible semidirect coordinates act on the ORIGINAL points. -/
def splitAffinePermutationHom : F.SplitAffineModel →* Equiv.Perm X where
  toFun g := F.affinePermutation g.right.val g.left.toAdd.val
  map_one' := by
    apply Equiv.ext
    intro x
    obtain ⟨⟨i, b⟩, rfl⟩ := F.frame.surjective x
    rw [F.affinePermutation_apply_frame]
    simp
  map_mul' g h := by
    rw [F.affinePermutation_mul_formula]
    congr 1 <;> rfl

/-- No source elements or original kernel correlations are identified. -/
theorem splitAffinePermutationHom_injective : Function.Injective F.splitAffinePermutationHom := by
  intro g h he
  have hh := F.affinePermutation_coordinates_injective he
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    exact Subtype.ext hh.2
  · exact Subtype.ext hh.1

/-- Full zero-model rows are exactly all actual kernel/top coordinate
pairs; no finite search establishes this completeness statement. -/
theorem splitAffinePermutationHom_range : F.splitAffinePermutationHom.range = F.splitAffineAction := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    exact Subgroup.subset_closure ⟨g.right, g.left.toAdd.val, g.left.toAdd.property, rfl⟩
  · apply (Subgroup.closure_le _).mpr
    rintro p ⟨t, a, ha, rfl⟩
    exact ⟨⟨Multiplicative.ofAdd ⟨a, ha⟩, t⟩, rfl⟩

/-- The original selected top generators suffice for the same zero model. -/
theorem splitAffinePermutationHom_range_eq_generated_model
    {J : Type} (u : J → U)
    (hgen : Subgroup.closure (Set.range fun i => F.top (u i)) = F.top.range) :
    F.splitAffinePermutationHom.range =
      F.affineGeneratedModel F.kernelSpace (fun i => F.top (u i)) (fun _ => 0) := by
  let f : F.SplitAffineModel →* F.top.range := SemidirectProduct.rightHom
  let lifts : J → F.SplitAffineModel := fun i => SemidirectProduct.inr (F.top.rangeRestrict (u i))
  have hfull : Subgroup.closure (Set.range fun i => f (lifts i)) = ⊤ :=
    F.top_lift_tuple_full u hgen
  have hh := range_eq_closure_kernel_and_actual_lifts f F.splitAffinePermutationHom lifts hfull
  have hk : Set.range (fun k : f.ker => F.splitAffinePermutationHom k.val) =
      {p | ∃ a ∈ F.kernelSpace, p = F.physicalFlip a} := by
    ext p
    constructor
    · rintro ⟨k, rfl⟩
      refine ⟨k.val.left.toAdd.val, k.val.left.toAdd.property, ?_⟩
      have ht : k.val.right = 1 := k.property
      change F.affinePermutation k.val.right.val k.val.left.toAdd.val =
        F.affinePermutation 1 k.val.left.toAdd.val
      rw [ht]
      rfl
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨SemidirectProduct.inl (Multiplicative.ofAdd ⟨a, ha⟩), rfl⟩, rfl⟩
  rw [hk] at hh
  exact hh

/-- A literal model equivalence, retaining the original point action. -/
def splitAffineModelEquiv : F.SplitAffineModel ≃* F.splitAffineAction :=
  (MonoidHom.ofInjective F.splitAffinePermutationHom_injective).trans
    (MulEquiv.subgroupCongr F.splitAffinePermutationHom_range)

end SymmetricSubgroupAsymptotics.BinaryPairFrame
