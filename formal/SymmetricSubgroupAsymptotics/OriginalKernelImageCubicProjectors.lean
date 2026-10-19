import SymmetricSubgroupAsymptotics.ElementaryKernelIntersectionFiltration

/-! Fixed and active projector ranks on the literal original elementary
image quotient. Group fixed-point-freeness is transported through the
actual quotient map, without constructing another denominator. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
variable {Q B D : Type} [Group Q] [Group B] [Group D]
  {eta : Q →* D} {A : Rep.{0} (ZMod 2) D}
  (E : OriginalKernelModuleChart eta A) (pi : Q →* B)

private theorem element_sub (v w : A) : E.element (v-w)=E.element v*(E.element w)⁻¹ := by
  change (E.equiv (Multiplicative.ofAdd (v-w)) : Q)=_
  rw [show Multiplicative.ofAdd (v-w)=Multiplicative.ofAdd v*(Multiplicative.ofAdd w)⁻¹ by simp [sub_eq_add_neg],
    map_mul,map_inv]
  rfl

theorem kernelImage_fixed_eq_zero (g : Q)
    (hfix : ∀ x∈(E.elementaryImageHom pi).range, pi g*x*(pi g)⁻¹=x → x=1)
    (v : A ⧸ (E.kernelIntersection pi).toSubmodule)
    (hv : E.kernelImageRepresentation pi g v=v) : v=0 := by
  let S := (E.kernelIntersection pi).toSubmodule
  obtain ⟨w,rfl⟩ := S.mkQ_surjective v
  have he : S.mkQ (A.ρ (eta g) w)=S.mkQ w := hv
  have hk : A.ρ (eta g) w-w∈S := by
    have hh : A.ρ (eta g) w-w∈S.mkQ.ker := by
      change S.mkQ (A.ρ (eta g) w-w)=0
      rw [map_sub,he,sub_self]
    rwa [Submodule.ker_mkQ] at hh
  have hh : pi (E.element (A.ρ (eta g) w-w))=1 := hk
  rw [E.element_sub,map_mul,map_inv] at hh
  have heq := mul_inv_eq_one.mp hh
  have hconj : pi g*pi (E.element w)*(pi g)⁻¹=pi (E.element w) := by
    have hh := E.conjugate g w
    change E.element (A.ρ (eta g) w)=g*E.element w*g⁻¹ at hh
    rw [← map_inv,← map_mul,← map_mul,← hh]
    exact heq
  have hx : pi (E.element w)=1 := hfix _ ⟨Multiplicative.ofAdd w,rfl⟩ hconj
  have hw : w∈S.mkQ.ker := by
    rw [Submodule.ker_mkQ]
    exact hx
  exact hw

variable [Finite A]

theorem kernelImage_dimension_le_two
    (hcard : Nat.card (E.elementaryImageHom pi).range≤4) :
    Module.finrank (ZMod 2) (A ⧸ (E.kernelIntersection pi).toSubmodule)≤2 := by
  let n := Module.finrank (ZMod 2) (A ⧸ (E.kernelIntersection pi).toSubmodule)
  have hp : 2^n≤4 := by
    rw [← E.kernelImage_card pi,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hcard
    exact hcard
  by_contra hn
  have h3 : 3≤n := by omega
  have hh : 2^3≤2^n := pow_le_pow_right₀ (by omega) h3
  norm_num at hh
  omega

theorem kernelImage_projector_ranks (g : Q) (hg : g^3=1)
    (hcard : Nat.card (E.elementaryImageHom pi).range≤4)
    (hfix : ∀ x∈(E.elementaryImageHom pi).range, pi g*x*(pi g)⁻¹=x → x=1) :
    let T := E.kernelImageRepresentation pi g
    Module.finrank (ZMod 2) (LinearMap.range (1+T+T^2))=0 ∧
      Module.finrank (ZMod 2) (LinearMap.range (T+T^2))≤2 := by
  let T := E.kernelImageRepresentation pi g
  have hc : T^3=1 := by rw [← map_pow,hg,map_one]
  have hz : (1+T+T^2 : Module.End (ZMod 2) _)=0 := by
    apply LinearMap.ext
    intro v
    apply E.kernelImage_fixed_eq_zero pi g hfix
    change T (v+T v+T (T v))=v+T v+T (T v)
    rw [map_add,map_add]
    have h3 : T (T (T v))=v := congrArg (fun f : Module.End (ZMod 2) _ => f v) hc
    rw [h3]
    abel
  constructor
  · rw [hz,LinearMap.range_zero]
    exact finrank_bot (ZMod 2) _
  · exact (Submodule.finrank_le _).trans (E.kernelImage_dimension_le_two pi hcard)

end SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
