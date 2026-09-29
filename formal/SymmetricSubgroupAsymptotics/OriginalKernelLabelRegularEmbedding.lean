import SymmetricSubgroupAsymptotics.OriginalKernelArbitraryNormalQuotient
import SymmetricSubgroupAsymptotics.RegularKernelHomBound

/-!
# Regular embeddings of binary sections from labelled coordinates

Let `E` chart an original binary kernel module `A` over a finite acting
quotient `B` of odd order.  Suppose `A` has injective additive coordinates
in the functions on a finite `B`-set of labels, compatible with conjugation,
and `B` is transitive on the labels.  Then for every original normal
subgroup `N`, the literal section `ker π / (ker π ∩ N)`, acted on by the
literal top `G / (ker π ⊔ N)`, embeds equivariantly in one copy of the
regular module of that top.

The proof averages a linear splitting over `B`; this is legitimate because
`|B|` is odd and the scalars have characteristic two.  One label evaluation
then gives a matrix coefficient whose translates separate the section.  No
classification of submodules, splitting of the group extension, or cyclicity
premise is used.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace OriginalKernelModuleChart

variable {G B : Type} [Group G] [Group B]
variable (π : G →* B) (A : Rep (ZMod 2) B) (E : OriginalKernelModuleChart π A)
variable (N : Subgroup G) [N.Normal]

/-- The section coordinate of an additive kernel vector. -/
theorem sectionMap_equiv_ofAdd (v : A) :
    (E.sectionMap π A N (E.equiv (Multiplicative.ofAdd v))).toAdd =
      (E.normalSpace π A N).mkQ v := by
  change (E.normalSpace π A N).mkQ
      ((E.equiv.symm (E.equiv (Multiplicative.ofAdd v))).toAdd) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- The literal quotient map from the kernel module to its section is
equivariant for the original ambient action. -/
theorem sectionRepresentation_mkQ (g : G) (v : A) :
    (E.sectionRepresentation π A N).ρ (QuotientGroup.mk' (π.ker ⊔ N) g)
        ((E.normalSpace π A N).mkQ v) =
      (E.normalSpace π A N).mkQ (A.ρ (π g) v) := by
  let k : π.ker := E.equiv (Multiplicative.ofAdd v)
  have hc : MulAut.conjNormal g k = E.equiv (Multiplicative.ofAdd (A.ρ (π g) v)) := by
    apply Subtype.ext
    rw [E.conjugate g v]
    rfl
  rw [← E.sectionMap_equiv_ofAdd π A N v, E.sectionRepresentation_apply, hc,
    E.sectionMap_equiv_ofAdd]

variable (hπ : Function.Surjective π)

/-- The literal acting top, factored from the original onto top map. -/
def labelTop : B →* G ⧸ (π.ker ⊔ N) :=
  π.liftOfSurjective hπ
    ⟨QuotientGroup.mk' (π.ker ⊔ N), by
      rw [QuotientGroup.ker_mk']
      exact le_sup_left⟩

@[simp] theorem labelTop_apply (g : G) :
    labelTop π N hπ (π g) = QuotientGroup.mk' (π.ker ⊔ N) g :=
  MonoidHom.liftOfRightInverse_comp_apply π (Function.surjInv hπ)
    (Function.rightInverse_surjInv hπ) _ g

theorem sectionRepresentation_mkQ_top (b : B) (v : A) :
    (E.normalSpace π A N).mkQ (A.ρ b v) =
      (E.sectionRepresentation π A N).ρ (labelTop π N hπ b)
        ((E.normalSpace π A N).mkQ v) := by
  obtain ⟨g, rfl⟩ := hπ b
  rw [labelTop_apply, E.sectionRepresentation_mkQ]

theorem natCast_eq_one_of_odd {n : ℕ} (hn : Odd n) : (n : ZMod 2) = 1 := by
  rw [← ZMod.natCast_mod n 2, Nat.odd_iff.mp hn]
  rfl

/-- An equivariant splitting of the section, obtained by averaging over the
odd acting quotient. -/
theorem exists_equivariant_splitting [Finite B] (hodd : Odd (Nat.card B)) :
    ∃ σ : (E.sectionModule π A N) →ₗ[ZMod 2] A,
      (∀ m, (E.normalSpace π A N).mkQ (σ m) = m) ∧
      ∀ (b : B) (m : E.sectionModule π A N),
        σ ((E.sectionRepresentation π A N).ρ (labelTop π N hπ b) m) = A.ρ b (σ m) := by
  letI : Fintype B := Fintype.ofFinite B
  let ρS := (E.sectionRepresentation π A N).ρ
  let τ := labelTop π N hπ
  obtain ⟨σ₀, hσ₀⟩ := (E.normalSpace π A N).mkQ.exists_rightInverse_of_surjective
    (Submodule.range_mkQ _)
  let σ : (E.sectionModule π A N) →ₗ[ZMod 2] A :=
    ∑ b : B, (A.ρ b).comp (σ₀.comp (ρS (τ b⁻¹)))
  have hσ (m : E.sectionModule π A N) :
      σ m = ∑ b : B, A.ρ b (σ₀ (ρS (τ b⁻¹) m)) := by
    change (∑ b : B, (A.ρ b).comp (σ₀.comp (ρS (τ b⁻¹)))) m = _
    rw [LinearMap.sum_apply]
    rfl
  refine ⟨σ, ?_, ?_⟩
  · intro m
    rw [hσ, map_sum]
    have hterm (b : B) : (E.normalSpace π A N).mkQ (A.ρ b (σ₀ (ρS (τ b⁻¹) m))) = m := by
      rw [E.sectionRepresentation_mkQ_top π A N hπ b]
      have hs : (E.normalSpace π A N).mkQ (σ₀ (ρS (τ b⁻¹) m)) = ρS (τ b⁻¹) m :=
        congrArg (fun f => f (ρS (τ b⁻¹) m)) hσ₀
      rw [hs, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_inv_cancel, map_one,
        map_one, Module.End.one_apply]
    rw [Finset.sum_congr rfl (fun b _ => hterm b), Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card]
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2), natCast_eq_one_of_odd hodd, one_smul]
  · intro c m
    rw [hσ, hσ, map_sum]
    rw [← Equiv.sum_comp (Equiv.mulLeft c)]
    apply Finset.sum_congr rfl
    intro b _
    simp only [Equiv.coe_mulLeft]
    rw [map_mul, Module.End.mul_apply]
    congr 2
    rw [← Module.End.mul_apply, ← map_mul, ← map_mul, mul_inv_rev, inv_mul_cancel_right]

variable {L : Type} [Finite L]

/-- Labelled coordinates embed every original-normal section in the regular
module of its literal acting top. -/
theorem section_regular_embedding_of_labels [Finite G] [Finite B]
    (hπ : Function.Surjective π) (hodd : Odd (Nat.card B))
    (act : B →* Equiv.Perm L) (htrans : ∀ s t : L, ∃ b : B, act b s = t)
    (κ : A →ₗ[ZMod 2] (L → ZMod 2)) (hκ : Function.Injective κ)
    (hequiv : ∀ (b : B) (v : A) (s : L), κ (A.ρ b v) (act b s) = κ v s)
    (s₀ : L) :
    ∃ F : (E.sectionRepresentation π A N).ρ.IntertwiningMap
      (Representation.leftRegular (ZMod 2) (G ⧸ (π.ker ⊔ N))),
      Function.Injective F := by
  letI : Fintype (G ⧸ (π.ker ⊔ N)) := Fintype.ofFinite _
  let S := G ⧸ (π.ker ⊔ N)
  let ρS := (E.sectionRepresentation π A N).ρ
  obtain ⟨σ, hsplit, hσ⟩ := E.exists_equivariant_splitting π A N hπ hodd
  let ℓ : (E.sectionModule π A N) →ₗ[ZMod 2] ZMod 2 :=
    (LinearMap.proj s₀).comp (κ.comp σ)
  let Φ : (E.sectionModule π A N) →ₗ[ZMod 2] (S → ZMod 2) :=
    LinearMap.pi (fun q : S => ℓ.comp (ρS q⁻¹))
  let F₀ : (E.sectionModule π A N) →ₗ[ZMod 2] (S →₀ ZMod 2) :=
    (Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) S).symm.toLinearMap.comp Φ
  have hF₀ (m : E.sectionModule π A N) (q : S) : F₀ m q = ℓ (ρS q⁻¹ m) := rfl
  let F : ρS.IntertwiningMap (Representation.leftRegular (ZMod 2) S) :=
    { toLinearMap := F₀
      isIntertwining' := by
        intro r
        apply LinearMap.ext
        intro m
        apply Finsupp.ext
        intro q
        change F₀ (ρS r m) q =
          Representation.ofMulAction (ZMod 2) S S r (F₀ m) q
        rw [Representation.ofMulAction_apply, hF₀, hF₀]
        have hq : (r⁻¹ • q)⁻¹ = q⁻¹ * r := by
          rw [smul_eq_mul, mul_inv_rev, inv_inv]
        rw [hq, map_mul, Module.End.mul_apply] }
  refine ⟨F, ?_⟩
  have hinj : Function.Injective F₀ := by
    rw [injective_iff_map_eq_zero]
    intro m hm
    have hℓ : ∀ q : S, ℓ (ρS q m) = 0 := by
      intro q
      have h := congrArg (fun f : S →₀ ZMod 2 => f q⁻¹) hm
      simp only [Finsupp.coe_zero, Pi.zero_apply] at h
      rwa [hF₀, inv_inv] at h
    have hzero : κ (σ m) = 0 := by
      funext s
      obtain ⟨b, hb⟩ := htrans s s₀
      rw [← hequiv b (σ m) s, hb, ← hσ b m]
      exact hℓ (labelTop π N hπ b)
    have hσm : σ m = 0 := hκ (hzero.trans (map_zero κ).symm)
    rw [← hsplit m, hσm, map_zero]
  exact hinj

end OriginalKernelModuleChart
end SymmetricSubgroupAsymptotics

end
