import SymmetricSubgroupAsymptotics.ChiefOrbitEvaluation
import Mathlib.GroupTheory.GroupAction.Basic

/-! Transitive original block coordinates identify the exact kernel of
the induced local-chief quotient. All original coordinate twists are
retained, and only their preservation of the literal lower local group
is required. The source need not be the full coordinate product. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {A N R X : Type} [Group A] [Group N] [Group R]
variable [MulAction A X] [MulAction.IsPretransitive A X]

def blockCoordinateKernel (θ : X→N→*R) (L : Subgroup R) : Subgroup N :=
  ⨅x:X,L.comap (θ x)

instance blockCoordinateKernel_normal (θ : X→N→*R) (L : Subgroup R) [L.Normal] :
    (blockCoordinateKernel θ L).Normal :=
  Subgroup.normal_iInf_normal (fun _=>inferInstance)

theorem mem_blockCoordinateKernel (θ : X→N→*R) (L : Subgroup R) (n:N) :
    n∈blockCoordinateKernel θ L ↔ ∀x:X,θ x n∈L := by
  simp only [blockCoordinateKernel,Subgroup.mem_iInf,Subgroup.mem_comap]

theorem translatedCoordinateKernel_iff (δ : A→*MulAut N)
    (θ : X→N→*R) (α : A→X→MulAut R) (L : Subgroup R) (x₀:X)
    (ht : ∀ (a:A) (x:X) (n:N),θ x (δ a n)=α a x (θ (a⁻¹•x) n))
    (hL : ∀ (a:A) (x:X),L.comap (α a x).toMonoidHom=L) (n:N) :
    (∀a:A,θ x₀ (δ a n)∈L) ↔ n∈blockCoordinateKernel θ L := by
  rw [mem_blockCoordinateKernel]
  constructor
  · intro h x
    obtain ⟨a,ha⟩ := MulAction.exists_smul_eq A x₀ x
    have hx := h a⁻¹
    rw [ht,inv_inv,ha] at hx
    change θ x n∈L.comap (α a⁻¹ x₀).toMonoidHom at hx
    rwa [hL] at hx
  · intro h a
    rw [ht]
    change θ (a⁻¹•x₀) n∈L.comap (α a x₀).toMonoidHom
    rw [hL]
    exact h _

theorem localChief_block_kernel {p : ℕ} [Fact p.Prime]
    [Finite A] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (δ : A→*MulAut N) (θ : X→N→*R) (α : A→X→MulAut R)
    (φ : R→*Multiplicative V) (x₀:X)
    (ht : ∀ (a:A) (x:X) (n:N),θ x (δ a n)=α a x (θ (a⁻¹•x) n))
    (hL : ∀ (a:A) (x:X),φ.ker.comap (α a x).toMonoidHom=φ.ker)
    (ρ : Representation (ZMod p) (MulAction.stabilizer A x₀) V)
    (he : ∀ (h:MulAction.stabilizer A x₀) (n:N),
      (φ (θ x₀ (δ (h:A) n))).toAdd=ρ h (φ (θ x₀ n)).toAdd) :
    (localChiefQuotientMap (MulAction.stabilizer A x₀) δ ρ (φ.comp (θ x₀)) he).ker=
      blockCoordinateKernel θ φ.ker := by
  ext n
  rw [localChiefQuotientMap_kernel]
  exact translatedCoordinateKernel_iff δ θ α φ.ker x₀ ht hL n

section Quotient
variable {p : ℕ} [Fact p.Prime] [Finite A]
variable {V : Type} [AddCommGroup V] [Module (ZMod p) V]
variable (δ : A→*MulAut N) (θ : X→N→*R) (α : A→X→MulAut R)
variable (φ : R→*Multiplicative V) (x₀:X)
variable (ht : ∀ (a:A) (x:X) (n:N),θ x (δ a n)=α a x (θ (a⁻¹•x) n))
variable (hL : ∀ (a:A) (x:X),φ.ker.comap (α a x).toMonoidHom=φ.ker)
variable (ρ : Representation (ZMod p) (MulAction.stabilizer A x₀) V)
variable (he : ∀ (h:MulAction.stabilizer A x₀) (n:N),
  (φ (θ x₀ (δ (h:A) n))).toAdd=ρ h (φ (θ x₀ n)).toAdd)

/-- The actual lower block kernel quotient is the actual induced image,
not an abstractly chosen module with the same dimension. -/
def localChiefBlockQuotientEquiv : N⧸blockCoordinateKernel θ φ.ker ≃*
    Multiplicative (localChiefInducedImage (MulAction.stabilizer A x₀)
      δ ρ (φ.comp (θ x₀)) he).toSubmodule :=
  (QuotientGroup.quotientMulEquivOfEq (localChief_block_kernel δ θ α φ x₀ ht hL ρ he).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (localChiefQuotientMap (MulAction.stabilizer A x₀) δ ρ (φ.comp (θ x₀)) he)
      (localChiefQuotientMap_surjective (MulAction.stabilizer A x₀) δ ρ (φ.comp (θ x₀)) he))

theorem localChiefBlockQuotientEquiv_apply (n:N) :
    localChiefBlockQuotientEquiv δ θ α φ x₀ ht hL ρ he (QuotientGroup.mk n)=
      localChiefQuotientMap (MulAction.stabilizer A x₀) δ ρ (φ.comp (θ x₀)) he n := rfl

/-- Conjugation or the given original external action is retained on
all actual quotient representatives. -/
theorem localChiefBlockQuotientEquiv_equivariant (a:A) (n:N) :
    localChiefBlockQuotientEquiv δ θ α φ x₀ ht hL ρ he (QuotientGroup.mk (δ a n))=
      representationGroupAction (localChiefInducedImage (MulAction.stabilizer A x₀)
        δ ρ (φ.comp (θ x₀)) he).toRepresentation a
        (localChiefBlockQuotientEquiv δ θ α φ x₀ ht hL ρ he (QuotientGroup.mk n)) :=
  localChiefQuotientMap_equivariant (MulAction.stabilizer A x₀) δ ρ (φ.comp (θ x₀)) he a n

end Quotient
end SymmetricSubgroupAsymptotics
