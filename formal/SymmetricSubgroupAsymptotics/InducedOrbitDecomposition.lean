import Mathlib.RepresentationTheory.FiniteIndex
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.Tactic

/-! Actual orbit decomposition of an induced representation restricted
to an original subgroup. We first split the coinduced function model by
literal H\G/P double-coset support and then transport through the
finite-index induction/coinduction equivalence. No decomposition or
filtration is assumed as an input. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
variable {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
variable (H P : Subgroup G) (ρ : Representation k H V)

theorem inducedOrbitLabel_left (h : H) (g : G) :
    DoubleCoset.mk H P ((h:G)*g)=DoubleCoset.mk H P g := by
  symm
  exact (DoubleCoset.eq H P g _).mpr ⟨h,h.2,1,P.one_mem,by simp⟩

theorem inducedOrbitLabel_right (g : G) (p : P) :
    DoubleCoset.mk H P (g*(p:G))=DoubleCoset.mk H P g := by
  symm
  exact (DoubleCoset.eq H P g _).mpr ⟨1,H.one_mem,p,p.2,by simp⟩

/-- The actual restricted coinduced representation. -/
abbrev coinducedRestriction : Representation k P (Representation.coindV H.subtype ρ) :=
  (Representation.coind H.subtype ρ).comp P.subtype

/-- Functions in the original coinduced module supported on one literal
double coset. This is an actual P-subrepresentation. -/
def coinducedOrbitPiece (q : DoubleCoset.Quotient (H:Set G) (P:Set G)) :
    Subrepresentation (coinducedRestriction H P ρ) where
  toSubmodule := {
    carrier := {f | ∀g,DoubleCoset.mk H P g≠q → f.1 g=0}
    zero_mem' := by simp
    add_mem' := by intro f f' hf hf' g hg; change f.1 g+f'.1 g=0; rw [hf g hg,hf' g hg,add_zero]
    smul_mem' := by intro a f hf g hg; simp [hf g hg] }
  apply_mem_toSubmodule p f hf := by
    intro g hg
    change f.1 (g*(p:G))=0
    exact hf _ (by simpa only [inducedOrbitLabel_right] using hg)

/-- The support projection in the actual function model. -/
def coinducedOrbitProjection (q : DoubleCoset.Quotient (H:Set G) (P:Set G)) :
    Representation.coindV H.subtype ρ →ₗ[k] (coinducedOrbitPiece H P ρ q).toSubmodule := by
  classical
  refine {
    toFun := fun f => ⟨⟨fun g => if DoubleCoset.mk H P g=q then f.1 g else 0,?_⟩,?_⟩
    map_add' := ?_
    map_smul' := ?_ }
  · intro h g
    simp only [H.subtype_apply,inducedOrbitLabel_left]
    split_ifs with he
    · exact f.2 h g
    · exact (map_zero (ρ h)).symm
  · intro g hg
    simp [hg]
  · intro f f'
    apply Subtype.ext
    apply Subtype.ext
    funext g
    change (if DoubleCoset.mk H P g=q then f.1 g+f'.1 g else 0)=
      (if DoubleCoset.mk H P g=q then f.1 g else 0)+
      (if DoubleCoset.mk H P g=q then f'.1 g else 0)
    split_ifs <;> simp
  · intro a f
    apply Subtype.ext
    apply Subtype.ext
    funext g
    change (if DoubleCoset.mk H P g=q then a • f.1 g else 0)=
      a • (if DoubleCoset.mk H P g=q then f.1 g else 0)
    split_ifs <;> simp

@[simp] theorem coinducedOrbitProjection_apply (q : DoubleCoset.Quotient (H:Set G) (P:Set G))
    (f : Representation.coindV H.subtype ρ) (g : G) :
    ((coinducedOrbitProjection H P ρ q f).1).1 g=
      if DoubleCoset.mk H P g=q then f.1 g else 0 := rfl

theorem coinducedOrbitProjection_equivariant (q : DoubleCoset.Quotient (H:Set G) (P:Set G))
    (p : P) (f : Representation.coindV H.subtype ρ) :
    coinducedOrbitProjection H P ρ q (coinducedRestriction H P ρ p f)=
      (coinducedOrbitPiece H P ρ q).toRepresentation p
        (coinducedOrbitProjection H P ρ q f) := by
  classical
  apply Subtype.ext
  apply Subtype.ext
  funext g
  change (if DoubleCoset.mk H P g=q then f.1 (g*(p:G)) else 0)=
    if DoubleCoset.mk H P (g*(p:G))=q then f.1 (g*(p:G)) else 0
  rw [inducedOrbitLabel_right]

variable [Fintype (DoubleCoset.Quotient (H:Set G) (P:Set G))]

/-- The inverse to the coordinate projections is the sum of the actual
supported functions, with each double coset used exactly once. -/
def coinducedOrbitSum :
    (∀q:DoubleCoset.Quotient (H:Set G) (P:Set G),(coinducedOrbitPiece H P ρ q).toSubmodule) →ₗ[k]
      Representation.coindV H.subtype ρ where
  toFun f := ∑q,(f q).1
  map_add' f f' := by simp [Finset.sum_add_distrib]
  map_smul' a f := by simp [Finset.smul_sum]

theorem coinducedOrbitSum_apply
    (f : ∀q:DoubleCoset.Quotient (H:Set G) (P:Set G),(coinducedOrbitPiece H P ρ q).toSubmodule) (g : G) :
    (coinducedOrbitSum H P ρ f).1 g=(f (DoubleCoset.mk H P g)).1.1 g := by
  classical
  change (∑q,(f q).1).1 g=_
  simp only [AddSubmonoidClass.coe_finsetSum,Finset.sum_apply]
  apply Finset.sum_eq_single (DoubleCoset.mk H P g)
  · intro q _ hq
    exact (f q).2 g hq.symm
  · simp

def coinducedOrbitDecomposition :
    Representation.coindV H.subtype ρ ≃ₗ[k]
      (∀q:DoubleCoset.Quotient (H:Set G) (P:Set G),(coinducedOrbitPiece H P ρ q).toSubmodule) where
  toFun f q := coinducedOrbitProjection H P ρ q f
  invFun := coinducedOrbitSum H P ρ
  left_inv f := by
    apply Subtype.ext
    funext g
    rw [coinducedOrbitSum_apply,coinducedOrbitProjection_apply]
    simp
  right_inv f := by
    funext q
    apply Subtype.ext
    apply Subtype.ext
    funext g
    rw [coinducedOrbitProjection_apply,coinducedOrbitSum_apply]
    split_ifs with h
    · subst q; rfl
    · exact ((f q).2 g h).symm
  map_add' f f' := by funext q; exact map_add _ _ _
  map_smul' a f := by funext q; exact map_smul _ _ _

variable [H.FiniteIndex]

/-- The finite-index isomorphism uses the actual original induction,
not a permutation representation with fibre twists discarded. -/
def inducedToCoinducedEquiv :
    (Representation.ind H.subtype ρ).Equiv (Representation.coind H.subtype ρ) :=
  Representation.equivOfIso (Rep.indCoindIso (Rep.of ρ))

/-- The original induced module, restricted to P, decomposes into its
literal double-coset support pieces. -/
def inducedOrbitDecomposition :
    Representation.IndV H.subtype ρ ≃ₗ[k]
      (∀q:DoubleCoset.Quotient (H:Set G) (P:Set G),(coinducedOrbitPiece H P ρ q).toSubmodule) :=
  (inducedToCoinducedEquiv H ρ).toLinearEquiv.trans (coinducedOrbitDecomposition H P ρ)

theorem inducedOrbitDecomposition_equivariant (p : P)
    (v : Representation.IndV H.subtype ρ)
    (q : DoubleCoset.Quotient (H:Set G) (P:Set G)) :
    inducedOrbitDecomposition H P ρ ((Representation.ind H.subtype ρ) (p:G) v) q=
      (coinducedOrbitPiece H P ρ q).toRepresentation p
        (inducedOrbitDecomposition H P ρ v q) := by
  change coinducedOrbitProjection H P ρ q
      ((inducedToCoinducedEquiv H ρ) ((Representation.ind H.subtype ρ) (p:G) v))=_
  have he : (inducedToCoinducedEquiv H ρ) ((Representation.ind H.subtype ρ) (p:G) v)=
      Representation.coind H.subtype ρ (p:G) ((inducedToCoinducedEquiv H ρ) v) :=
    Representation.IntertwiningMap.isIntertwining _ _
      (inducedToCoinducedEquiv H ρ).toIntertwiningMap (p:G) v
  rw [he]
  exact coinducedOrbitProjection_equivariant H P ρ q p _

end SymmetricSubgroupAsymptotics
