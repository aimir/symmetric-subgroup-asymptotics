import SymmetricSubgroupAsymptotics.FiniteGeneratorGraphEquivalence
import SymmetricSubgroupAsymptotics.FiniteKernelCosetSignature

/-! A bounded quotient-word graph with actual kernel residues. The original
group is never enumerated: each target edge is checked modulo the displayed
finite original kernel, and point-code coset signatures give exactness. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
open FiniteKernelCosetSignature

structure FiniteKernelQuotientWordGraph {G H R I J : Type}
    [Group G] [Group H] [Group R] [Fintype R]
    (kappa : R →* G) [kappa.range.Normal]
    (source : J → G) (target : J → H) (code : G → ℕ) where
  word : I → List J
  identity : I
  identity_source : ((word identity).map source).prod=1
  identity_target : ((word identity).map target).prod=1
  step : I → J → I
  step_residue : I → J → R
  step_source : ∀ i j,
    ((word (step i j)).map source).prod*kappa (step_residue i j)=
      ((word i).map source).prod*source j
  step_target : ∀ i j,
    ((word (step i j)).map target).prod=((word i).map target).prod*target j
  inverse : I → I
  inverse_residue : I → R
  inverse_source : ∀ i,
    ((word (inverse i)).map source).prod*kappa (inverse_residue i)=
      (((word i).map source).prod)⁻¹
  inverse_target : ∀ i,
    ((word (inverse i)).map target).prod=(((word i).map target).prod)⁻¹
  target_word_injective : Function.Injective (fun i => ((word i).map target).prod)
  signature_injective : Function.Injective
    (fun i => signature kappa code (((word i).map source).prod))

namespace FiniteKernelQuotientWordGraph
variable {G H R I J : Type} [Group G] [Group H] [Group R] [Fintype R]
  {kappa : R →* G} [kappa.range.Normal]
  {source : J → G} {target : J → H} {code : G → ℕ}
  (C : FiniteKernelQuotientWordGraph (I := I) kappa source target code)

private theorem word_pair (w : List J) :
    (w.map (fun j => (target j,QuotientGroup.mk' kappa.range (source j)))).prod=
      ((w.map target).prod,QuotientGroup.mk' kappa.range ((w.map source).prod)) := by
  induction w with
  | nil => change (1,1) = (1,1); rfl
  | cons j w ih => simp only [List.map_cons,List.prod_cons,ih,map_mul]; rfl

private theorem mk_kernel (r : R) : QuotientGroup.mk' kappa.range (kappa r)=1 :=
  (QuotientGroup.eq_one_iff _).mpr ⟨r,rfl⟩

/-- The finite graph runs from the literal target to the original quotient. -/
def certificate : FiniteGeneratorGraphCertificate (I := I) target
    (fun j => QuotientGroup.mk' kappa.range (source j)) where
  state i := (((C.word i).map target).prod,
    QuotientGroup.mk' kappa.range (((C.word i).map source).prod))
  word := C.word
  word_eq i := word_pair (C.word i)
  identity := C.identity
  identity_eq := by rw [C.identity_source,C.identity_target,map_one]; rfl
  step := C.step
  step_eq i j := by
    apply Prod.ext
    · exact C.step_target i j
    · have h := congrArg (QuotientGroup.mk' kappa.range) (C.step_source i j)
      simpa only [map_mul,mk_kernel,mul_one] using h
  inverse := C.inverse
  inverse_eq i := by
    apply Prod.ext
    · exact C.inverse_target i
    · have h := congrArg (QuotientGroup.mk' kappa.range) (C.inverse_source i)
      simpa only [map_mul,map_inv,mk_kernel,mul_one] using h
  source_injective := C.target_word_injective

/-- Quotient equality cannot identify two distinct finite target states. -/
theorem quotient_state_injective : Function.Injective
    (fun i => (C.certificate.state i).2) := by
  intro i j h
  apply C.signature_injective
  exact signature_eq_of_quotient_eq kappa code h

def equivalence : C.certificate.Source ≃* C.certificate.Target :=
  C.certificate.equiv C.quotient_state_injective
end FiniteKernelQuotientWordGraph
end SymmetricSubgroupAsymptotics
