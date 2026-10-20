import SymmetricSubgroupAsymptotics.OriginalEquivariantQuotientEmbedding

/-! The kernel on any nonzero actual submodule of a faithful transitive
monomial representation injects into the actual block image. An actual
subquotient has the same bound when the finite acting order is invertible.
No sign-character census or independent-coordinate hypothesis is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.TransitiveMonomialSubquotientKernel

variable {k H P I W : Type} [Field k] [Group H] [Group P] [MulAction P I]
  [AddCommGroup W] [Module k W]
  (rho : Representation k H (I → k)) (top : H →* P) (d : H → I → k)
  (happly : ∀ (g : H) (v : I → k) (i : I),
    rho g v i=d g i*v ((top g)⁻¹ • i))
  (hunit : ∀ g i, d g i≠0) (hfaithful : Function.Injective rho)
  (htrans : ∀ i j : I, ∃ g : H, top g • i=j)

include rho d happly hunit hfaithful htrans in
/-- A base element fixing a nonzero actual submodule fixes every coordinate
scalar: transport one nonzero coordinate through the actual block action. -/
theorem eq_one_of_fixed_top_one (sigma : Representation k H W) [Nontrivial W]
    (f : Representation.IntertwiningMap sigma rho) (hf : Function.Injective f)
    (g : H) (hg : ∀ w : W, sigma g w=w) (htop : top g=1) : g=1 := by
  obtain ⟨w,hw⟩ := exists_ne (0 : W)
  have hfw : f w≠0 := by
    intro h
    apply hw
    apply hf
    simpa only [map_zero] using h
  have hcoord : ∃ i : I, f w i≠0 := by
    by_contra hn
    push_neg at hn
    apply hfw
    funext i
    exact hn i
  obtain ⟨i₀,hi₀⟩ := hcoord
  have hscalar : ∀ t : I, d g t=1 := by
    intro t
    obtain ⟨h,hh⟩ := htrans i₀ t
    have hindex : (top h)⁻¹ • t=i₀ := by rw [← hh,inv_smul_smul]
    have heq : f (sigma h w) t=d h t*f w i₀ := by
      have he := congrFun (Representation.IntertwiningMap.isIntertwining sigma rho f h w) t
      rw [happly,hindex] at he
      exact he
    have hnonzero : f (sigma h w) t≠0 := by
      rw [heq]
      exact mul_ne_zero (hunit h t) hi₀
    have he := congrFun
      (Representation.IntertwiningMap.isIntertwining sigma rho f g (sigma h w)) t
    rw [hg (sigma h w)] at he
    have he' : d g t*f (sigma h w) t=1*f (sigma h w) t := by
      simpa only [happly,htop,inv_one,one_smul,one_mul] using he.symm
    exact mul_right_cancel₀ hnonzero he'
  apply hfaithful
  rw [map_one]
  apply LinearMap.ext
  intro v
  funext i
  change rho g v i=v i
  rw [happly,hscalar i,htop,inv_one,one_smul,one_mul]

include rho d happly hunit hfaithful htrans in
/-- The actual acting kernel on a nonzero injected module injects into the
actual block group, rather than into a worst-case scalar comparator. -/
theorem kernel_top_injective (sigma : Representation k H W) [Nontrivial W]
    (f : Representation.IntertwiningMap sigma rho) (hf : Function.Injective f) :
    Function.Injective (top.comp sigma.asGroupHom.ker.subtype) := by
  intro x y hxy
  apply Subtype.ext
  have hx : sigma.asGroupHom (x : H)=1 := x.property
  have hy : sigma.asGroupHom (y : H)=1 := y.property
  have hker : sigma.asGroupHom ((x : H)*(y : H)⁻¹)=1 := by
    rw [map_mul,map_inv,hx,hy,inv_one,one_mul]
  have hfixed : ∀ w : W, sigma ((x : H)*(y : H)⁻¹) w=w := by
    intro w
    exact congrArg (fun z : (Module.End k W)ˣ => (z : Module.End k W) w) hker
  have ht : top ((x : H)*(y : H)⁻¹)=1 := by
    change top (x : H)=top (y : H) at hxy
    rw [map_mul,map_inv,hxy,mul_inv_cancel]
  have hone := eq_one_of_fixed_top_one rho top d happly hunit hfaithful htrans
    sigma f hf ((x : H)*(y : H)⁻¹) hfixed ht
  exact mul_inv_eq_one.mp hone

include rho d happly hunit hfaithful htrans in
theorem kernel_card_le [Finite P] (sigma : Representation k H W) [Nontrivial W]
    (f : Representation.IntertwiningMap sigma rho) (hf : Function.Injective f) :
    Nat.card sigma.asGroupHom.ker≤Nat.card P := by
  have hinj := kernel_top_injective rho top d happly hunit hfaithful htrans sigma f hf
  letI : Finite sigma.asGroupHom.ker := Finite.of_injective _ hinj
  exact Nat.card_le_card_of_injective _ hinj

include rho d happly hunit hfaithful htrans in
/-- Maschke is applied only to the actual finite acting group on this
ternary module. The supplied original quotient map is retained explicitly. -/
theorem subquotient_kernel_card_le [Finite H] [Finite P]
    [NeZero (Nat.card H : k)] (S : Subrepresentation rho)
    (sigma : Representation k H W) [Nontrivial W]
    (q : Representation.IntertwiningMap S.toRepresentation sigma)
    (hq : Function.Surjective q) : Nat.card sigma.asGroupHom.ker≤Nat.card P := by
  obtain ⟨i,hi⟩ := original_equivariant_quotient_embedding S.toRepresentation sigma q hq
  let inclusion : Representation.IntertwiningMap S.toRepresentation rho :=
    { toLinearMap := S.toSubmodule.subtype
      isIntertwining' _ := rfl }
  exact kernel_card_le rho top d happly hunit hfaithful htrans sigma
    (inclusion.comp i) (Subtype.val_injective.comp hi)

end SymmetricSubgroupAsymptotics.TransitiveMonomialSubquotientKernel
