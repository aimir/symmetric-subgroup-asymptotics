import SymmetricSubgroupAsymptotics.CFSGHyperbolicSingularSpanning
import SymmetricSubgroupAsymptotics.CFSGTwoFunctionalKernelVector

/-! A nonzero functional on a hyperbolic pair's actual perpendicular
complement detects an actual singular vector there. The hyperbolic pair
inside that complement is CONSTRUCTED from the original singular
subspace and ambient nondegeneracy, rather than supplied as a premise. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHyperbolicPerpSingularWitness
open CFSGHyperbolicPlaneProjection CFSGHyperbolicSingularSpanning
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem exists_singular_perp_not_killed (B : LinearMap.BilinForm K V)
    (h2 : (2 : K) ≠ 0) (hs : ∀ x y, B x y = B y x)
    (hn : ∀ e, (∀ x, B e x = 0) → e = 0)
    (P : Submodule K V) (hP : 3 ≤ Module.finrank K P)
    (hPs : ∀ x ∈ P, B x x = 0)
    (v w : V) (hv : B v v = 0) (hw : B w w = 0) (hc : B v w ≠ 0)
    (l : V →ₗ[K] K) (hl : l.comp (perp B v w).subtype ≠ 0) :
    ∃ x : V, x ∈ perp B v w ∧ B x x = 0 ∧ l x ≠ 0 := by
  obtain ⟨e, heP, he, hev, hew⟩ :=
    CFSGTwoFunctionalKernelVector.exists_nonzero_common_kernel P hP (B v) (B w)
  let C := perp B v w
  let BC := B.restrict C
  let eC : C := ⟨e, hev, hew⟩
  have hsC (x y : C) : BC x y = BC y x := hs x.val y.val
  have hnC (z : C) (hz : ∀ x : C, BC z x = 0) : z = 0 := by
    apply Subtype.ext
    apply perp_nondegenerate B hs hn v w hv hw hc z.val z.property
    intro x hx
    exact hz ⟨x, hx⟩
  have heC : eC ≠ 0 := by intro hh; exact he (congrArg Subtype.val hh)
  have heC0 : BC eC eC = 0 := hPs e heP
  obtain ⟨fC, hfC, hefC⟩ := exists_hyperbolic_partner BC h2 hsC hnC eC heC heC0
  obtain ⟨x, hx, hlx⟩ := exists_singular_not_killed BC h2 hsC eC fC heC0 hfC hefC
    (l.comp C.subtype) hl
  exact ⟨x.val, x.property, hx, hlx⟩

end SymmetricSubgroupAsymptotics.CFSGHyperbolicPerpSingularWitness
