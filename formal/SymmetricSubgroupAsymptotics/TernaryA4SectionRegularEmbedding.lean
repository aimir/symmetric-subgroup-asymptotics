import SymmetricSubgroupAsymptotics.TernaryA4InvariantSubmodules
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RepresentationTheory.Intertwining

/-!
# Every descended section of the four-coordinate ternary module

Each natural-A4 invariant denominator has an equivariant linear map with
exactly that kernel. Consequently every invariant section embeds back into
the original four-coordinate module. One matrix coefficient then embeds
the section in the regular function representation of any group through
which its action factors. The quotient map and its original action are
retained; no splitting of a group extension is involved.

For a finite quotient Q, functions Q → F3 are the finite regular module.
The construction works even without finiteness or surjectivity, so those
hypotheses need not be manufactured inside the linear argument.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.TernaryA4SectionRegularEmbedding

open TernaryA4InvariantSubmodules

def diagonalProjection : V →ₗ[Scalar] V where
  toFun v _ := ∑ i, v i
  map_add' v w := by
    funext i
    exact Finset.sum_add_distrib
  map_smul' a v := by
    funext i
    change (∑ j, a * v j) = a * ∑ j, v j
    exact (Finset.mul_sum _ _ _).symm

def augmentationProjection : V →ₗ[Scalar] V := LinearMap.id - diagonalProjection

theorem diagonalProjection_kernel : diagonalProjection.ker = augmentation := by
  ext v
  constructor
  · intro hv
    exact congrFun (LinearMap.mem_ker.mp hv) 0
  · intro hv
    apply LinearMap.mem_ker.mpr
    funext i
    exact hv

private theorem augmentationProjection_zero_iff : ∀ v : V,
    augmentationProjection v = 0 ↔ ∀ i, v i = v 0 := by
  decide +kernel

theorem augmentationProjection_kernel : augmentationProjection.ker = diagonal := by
  ext v
  exact augmentationProjection_zero_iff v

theorem diagonalProjection_equivariant (g : Equiv.Perm (Fin 4)) (v : V) :
    diagonalProjection (coordinateAction g v) = coordinateAction g (diagonalProjection v) := by
  funext i
  change (∑ j, v (g.symm j)) = ∑ j, v j
  exact Equiv.sum_comp g.symm v

theorem augmentationProjection_equivariant (g : Equiv.Perm (Fin 4)) (v : V) :
    augmentationProjection (coordinateAction g v) =
      coordinateAction g (augmentationProjection v) := by
  change coordinateAction g v - diagonalProjection (coordinateAction g v) =
    coordinateAction g (v - diagonalProjection v)
  rw [map_sub, diagonalProjection_equivariant]

/-- Equivariant complements are proved for every actual invariant
denominator, including zero and the whole module. -/
theorem exists_equivariant_map_with_kernel (C : Submodule Scalar V) (hC : Invariant C) :
    ∃ P : V →ₗ[Scalar] V, P.ker = C ∧
      ∀ (g : A4) (v : V), P (coordinateAction g.1 v) = coordinateAction g.1 (P v) := by
  rcases classification C hC with rfl | rfl | rfl | rfl
  · exact ⟨LinearMap.id, LinearMap.ker_id, fun _ _ => rfl⟩
  · exact ⟨augmentationProjection, augmentationProjection_kernel,
      fun g v => augmentationProjection_equivariant g.1 v⟩
  · exact ⟨diagonalProjection, diagonalProjection_kernel,
      fun g v => diagonalProjection_equivariant g.1 v⟩
  · refine ⟨0, LinearMap.ker_zero, ?_⟩
    intro g v
    exact (map_zero (coordinateAction g.1)).symm

/-- The literal section B/(B∩C). When C≤B this is the usual B/C; using
the comap avoids replacing an original denominator by an isomorphic type. -/
abbrev Section (B C : Submodule Scalar V) := B ⧸ C.comap B.subtype

abbrev sectionMk (B C : Submodule Scalar V) : B →ₗ[Scalar] Section B C :=
  (C.comap B.subtype).mkQ

variable {Q : Type*} [Group Q]

/-- Exact factorization of the original A4 action on every original
quotient representative. This is structural data, not an embedding premise. -/
def FactorsSection (B C : Submodule Scalar V) (hB : Invariant B)
    (β : A4 →* Q) (ρ : Representation Scalar Q (Section B C)) : Prop :=
  ∀ (g : A4) (v : B), ρ (β g) (sectionMk B C v) =
    sectionMk B C ⟨coordinateAction g.1 v.1, hB g.1 g.2 v.1 v.2⟩

theorem section_embedding_in_coordinates (B C : Submodule Scalar V)
    (hB : Invariant B) (hC : Invariant C)
    (β : A4 →* Q) (ρ : Representation Scalar Q (Section B C))
    (hρ : FactorsSection B C hB β ρ) :
    ∃ E : Section B C →ₗ[Scalar] V, Function.Injective E ∧
      ∀ (g : A4) (v : Section B C), E (ρ (β g) v) = coordinateAction g.1 (E v) := by
  obtain ⟨P, hP, hPE⟩ := exists_equivariant_map_with_kernel C hC
  have hker : (P.comp B.subtype).ker = C.comap B.subtype := by
    rw [LinearMap.ker_comp, hP]
  let E : Section B C →ₗ[Scalar] V :=
    (C.comap B.subtype).liftQ (P.comp B.subtype) hker.ge
  refine ⟨E, ?_, ?_⟩
  · apply LinearMap.ker_eq_bot.mp
    exact (C.comap B.subtype).ker_liftQ_eq_bot (P.comp B.subtype) hker.ge hker.le
  · intro g v
    obtain ⟨v, rfl⟩ := (C.comap B.subtype).mkQ_surjective v
    rw [hρ g v]
    exact hPE g v.1

/-- Left regular action on functions. For finite Q this is precisely the
finite regular module, without choosing a list of its original elements. -/
def regularFunctions (k Q : Type*) [Field k] [Group Q] :
    Representation k Q (Q → k) where
  toFun q := {
    toFun f x := f (q⁻¹ * x)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  map_one' := by
    ext f x
    change f ((1 : Q)⁻¹ * x) = f x
    rw [inv_one, one_mul]
  map_mul' q r := by
    ext f x
    change f ((q * r)⁻¹ * x) = f (r⁻¹ * (q⁻¹ * x))
    rw [mul_inv_rev, mul_assoc]

section MatrixCoefficient

variable {k M : Type*} [Field k] [AddCommGroup M] [Module k M]

/-- A matrix coefficient written on the same original quotient Q. -/
def matrixCoefficient (ρ : Representation k Q M) (ℓ : M →ₗ[k] k) :
    M →ₗ[k] (Q → k) where
  toFun v q := ℓ (ρ q⁻¹ v)
  map_add' v w := by
    funext q
    simp only [map_add, Pi.add_apply]
  map_smul' a v := by
    funext q
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

theorem matrixCoefficient_equivariant (ρ : Representation k Q M) (ℓ : M →ₗ[k] k)
    (q : Q) (v : M) :
    matrixCoefficient ρ ℓ (ρ q v) = regularFunctions k Q q (matrixCoefficient ρ ℓ v) := by
  funext x
  change ℓ (ρ x⁻¹ (ρ q v)) = ℓ (ρ ((q⁻¹ * x)⁻¹) v)
  rw [mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply]

end MatrixCoefficient

private theorem a4_reaches_zero : ∀ i : Fin 4, ∃ g : A4, (g : Equiv.Perm (Fin 4)) 0 = i := by
  decide +kernel

/-- Every invariant section embeds in the regular function module of its
actual quotient action. In particular this holds for EVERY onto quotient
of A4, including the trivial quotient and all original normal axes. -/
theorem descended_regular_embedding (B C : Submodule Scalar V)
    (hB : Invariant B) (hC : Invariant C)
    (β : A4 →* Q) (ρ : Representation Scalar Q (Section B C))
    (hρ : FactorsSection B C hB β ρ) :
    ∃ F : ρ.IntertwiningMap (regularFunctions Scalar Q), Function.Injective F := by
  obtain ⟨E, hE, hEE⟩ := section_embedding_in_coordinates B C hB hC β ρ hρ
  let ℓ : Section B C →ₗ[Scalar] Scalar := {
    toFun v := E v 0
    map_add' v w := congrFun (E.map_add v w) 0
    map_smul' a v := congrFun (E.map_smul a v) 0 }
  let F : ρ.IntertwiningMap (regularFunctions Scalar Q) :=
    (matrixCoefficient ρ ℓ).intertwiningMap_of_isIntertwiningMap
      ρ (regularFunctions Scalar Q) (matrixCoefficient_equivariant ρ ℓ)
  refine ⟨F, ?_⟩
  intro v w hvw
  apply hE
  funext i
  obtain ⟨g, hg⟩ := a4_reaches_zero i
  have h := congrFun hvw (β g)
  change E (ρ (β g)⁻¹ v) 0 = E (ρ (β g)⁻¹ w) 0 at h
  rw [← map_inv, hEE, hEE] at h
  change E v ((g : Equiv.Perm (Fin 4)) 0) = E w ((g : Equiv.Perm (Fin 4)) 0) at h
  rwa [hg] at h

/-- The onto-quotient version lands in Mathlib's actual group-algebra
regular representation. Finiteness of Q follows from the original β. -/
theorem descended_groupAlgebra_embedding (B C : Submodule Scalar V)
    (hB : Invariant B) (hC : Invariant C)
    (β : A4 →* Q) (hβ : Function.Surjective β)
    (ρ : Representation Scalar Q (Section B C))
    (hρ : FactorsSection B C hB β ρ) :
    ∃ F : ρ.IntertwiningMap (Representation.leftRegular Scalar Q), Function.Injective F := by
  letI : Finite Q := Finite.of_surjective β hβ
  obtain ⟨F, hF⟩ := descended_regular_embedding B C hB hC β ρ hρ
  let T : (Q → Scalar) ≃ₗ[Scalar] (Q →₀ Scalar) :=
    (Finsupp.linearEquivFunOnFinite Scalar Scalar Q).symm
  have hT (q : Q) (f : Q → Scalar) :
      T (regularFunctions Scalar Q q f) = Representation.leftRegular Scalar Q q (T f) := by
    ext x
    rw [Representation.ofMulAction_apply]
    rfl
  let F' : ρ.IntertwiningMap (Representation.leftRegular Scalar Q) := {
    toLinearMap := T.toLinearMap.comp F.toLinearMap
    isIntertwining' q := by
      apply LinearMap.ext
      intro v
      change T (F (ρ q v)) = Representation.leftRegular Scalar Q q (T (F v))
      rw [F.isIntertwining, hT] }
  exact ⟨F', T.injective.comp hF⟩

end SymmetricSubgroupAsymptotics.TernaryA4SectionRegularEmbedding

end
