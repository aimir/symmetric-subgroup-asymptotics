import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleGradedDerivedAction
import SymmetricSubgroupAsymptotics.CFSGReeFFourAllParameterDerivedPositive
import SymmetricSubgroupAsymptotics.CFSGCentralKernelPSubgroups

/-! Faithful descent of the literal derived graded 2-kernel through the
FULL centre quotient defining the original model. Opposed Sylows and
the actual central-p-element theorem eliminate its central kernel. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleGradedOriginalImage
open CFSGReeFFourMiddleGradedDerivedAction CFSGReeFFourMiddleDerivedFiveSurvival
open CFSGReeFFourAllParameterDerivedPositive CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourOriginalPositiveSylow CFSGReeFFourFixedAmbientHom
open CFSGDisjointSylowProjectiveCardinality CFSGCentralKernelPElements
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private instance fixedFinite (m : ℕ) : Finite (originalModelFixed m) :=
  Finite.of_injective (fixedAmbientHom m) (fixedAmbientHom_injective m)

def kernelToOriginal (m : ℕ) : derivedGradedKernel m →* CFSG.Models.ReeF4 m :=
  (derivedReeHom m).comp (kernelToDerived m)

private theorem quotient_injective_of_pgroup {G N : Type*} [Group G] [Group N]
    (P Q : Sylow 2 G) (hPQ : (P : Subgroup G) ⊓ (Q : Subgroup G) = ⊥)
    (psi : N →* G) (hpsi : Function.Injective psi) (hN : IsPGroup 2 N) :
    Function.Injective ((QuotientGroup.mk' (Subgroup.center G)).comp psi) := by
  let q := QuotientGroup.mk' (Subgroup.center G)
  have hP := central_quotient_injective P Q hPQ
  have hker : q.ker ≤ Subgroup.center G := by
    change (QuotientGroup.mk' (Subgroup.center G)).ker ≤ Subgroup.center G
    rw [QuotientGroup.ker_mk']
  intro x y h
  obtain ⟨a,ha⟩ := hN x
  obtain ⟨b,hb⟩ := hN y
  have hx : ∃ n : ℕ, (psi x)^(2^n) = 1 := by
    refine ⟨a, ?_⟩
    exact (map_pow psi x (2^a)).symm.trans ((congrArg psi ha).trans (map_one psi))
  have hy : ∃ n : ℕ, (psi y)^(2^n) = 1 := by
    refine ⟨b, ?_⟩
    exact (map_pow psi y (2^b)).symm.trans ((congrArg psi hb).trans (map_one psi))
  apply hpsi
  exact eq_of_p_elements q P hP hker _ _ hx hy h

theorem kernelToOriginal_injective (m : ℕ) : Function.Injective (kernelToOriginal m) := by
  have hi := quotient_injective_of_pgroup (positiveSylow m) (negativeSylow m) (opposite_inf m)
    (kernelToDerived m) (kernelToDerived_injective m) (derivedGradedKernel_isPGroup m)
  intro x y h
  apply hi
  apply (originalReeEquiv m).symm.injective
  exact h

instance derivedGradedKernel_finite (m : ℕ) : Finite (derivedGradedKernel m) :=
  Finite.of_injective (kernelToDerived m) (kernelToDerived_injective m)

def kernelImage (m : ℕ) : Subgroup (CFSG.Models.ReeF4 m) := (kernelToOriginal m).range

def kernelEquivImage (m : ℕ) : derivedGradedKernel m ≃* kernelImage m :=
  MonoidHom.ofInjective (kernelToOriginal_injective m)

instance kernelImage_finite (m : ℕ) : Finite (kernelImage m) :=
  Finite.of_equiv (derivedGradedKernel m) (kernelEquivImage m).toEquiv

theorem kernelImage_isPGroup (m : ℕ) : IsPGroup 2 (kernelImage m) :=
  (derivedGradedKernel_isPGroup m).of_equiv (kernelEquivImage m)

private theorem transport_conjugation {D N O : Type*} [Group D] [Group N] [Group O]
    (f : D →* O) (j : N →* D) (phi : MulAut N) (d : D)
    (h : ∀ n, j (phi n) = d * j n * d⁻¹) (n : N) :
    (f.comp j) (phi n) = f d * (f.comp j) n * (f d)⁻¹ := by
  change f (j (phi n)) = _
  calc
    f (j (phi n)) = f (d * j n * d⁻¹) := congrArg f (h n)
    _ = f d * (f.comp j) n * (f d)⁻¹ := by rw [map_mul, map_mul, map_inv]; rfl

private theorem normalizes_range {N G : Type*} [Group N] [Group G]
    (f : N →* G) (phi : MulAut N) (g : G)
    (h : ∀ n, f (phi n) = g * f n * g⁻¹) :
    g ∈ Subgroup.normalizer (f.range : Set G) := by
  intro n
  constructor
  · rintro ⟨u,rfl⟩
    exact ⟨phi u,h u⟩
  · rintro ⟨u,hu⟩
    refine ⟨phi.symm u, ?_⟩
    have ht := h (phi.symm u)
    rw [phi.apply_symm_apply] at ht
    apply (MulAut.conj g).injective
    exact ht.symm.trans hu

theorem kernelToOriginal_fiveAction (m : ℕ) (u : derivedGradedKernel m) :
    kernelToOriginal m (fiveAction m u) =
      originalFiveWord m * kernelToOriginal m u * (originalFiveWord m)⁻¹ :=
  transport_conjugation (derivedReeHom m) (kernelToDerived m) (fiveAction m)
    (CFSGReeFFourMiddleDerivedFiveWord.derivedFiveWord m)
    (kernelToDerived_conjugation m (derivedParabolicFiveWord m)) u

theorem originalFiveWord_normalizes_image (m : ℕ) :
    originalFiveWord m ∈ Subgroup.normalizer (kernelImage m : Set (CFSG.Models.ReeF4 m)) :=
  normalizes_range (kernelToOriginal m) (fiveAction m) (originalFiveWord m)
    (kernelToOriginal_fiveAction m)

def imageFiveAction (m : ℕ) : MulAut (kernelImage m) :=
  MulAut.congr (kernelEquivImage m) (fiveAction m)

theorem imageFiveAction_order (m : ℕ) : orderOf (imageFiveAction m) = 5 :=
  ((MulAut.congr (kernelEquivImage m)).orderOf_eq (fiveAction m)).trans (fiveAction_order m)

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleGradedOriginalImage
