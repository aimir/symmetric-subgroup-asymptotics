import SymmetricSubgroupAsymptotics.CFSGPolarSubspaceOpposition
import SymmetricSubgroupAsymptotics.CFSGPolarPointFunctionals

/-! After a polar point map fixes a maximal singular space pointwise,
stabilizing a disjoint singular space forces it to fix that space
pointwise too. This follows from actual restricted functionals and their
nondegenerate cross-pairing, without a polar recognition hypothesis. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints
open CFSGSingularPlaneTriangle
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem fixes_opposite_points (B : LinearMap.BilinForm K V) (hs : ∀x y,B x y=B y x)
    (d : ℕ) (hbound : ∀T : Subspaces B,Module.finrank K T.val≤d)
    (f : Points B≃Points B)
    (horth : ∀P Q,ZeroOn B (f P).val (f Q).val ↔ ZeroOn B P.val Q.val)
    (W Z : Subspaces B) (hW : Module.finrank K W.val=d)
    (hdisjoint : (W.val⊓Z.val : Submodule K V)=⊥)
    (hfix : ∀Q : Points B,Q.val≤W.val → f Q=Q)
    (hstable : ∀P : Points B,P.val≤Z.val → (f P).val≤Z.val) :
    ∀P : Points B,P.val≤Z.val → f P=P := by
  intro P hP
  obtain ⟨x,hx,hx0⟩ := point_nonzero B P
  obtain ⟨y,hy,hy0⟩ := point_nonzero B (f P)
  have hd : (Z.val⊓W.val : Submodule K V)=⊥ := by rw [inf_comm,hdisjoint]
  have hnondeg (v : V) (hv : v∈Z.val) (hz : ∀w∈W.val,B v w=0) : v=0 :=
    opposed_pair_left_nondegenerate B hs d hbound Z W hW hd v hv hz
  have hn : restrictedPairing B W x≠0 := by
    intro hz
    apply hx0
    apply hnondeg x (hP hx)
    intro w hw
    exact LinearMap.congr_fun hz ⟨w,hw⟩
  obtain ⟨c,hc,he⟩ := restrictedPairing_proportional B f horth W hfix P x y hx hy hx0 hy0 hn
  have hv : y-c•x∈Z.val := Z.val.sub_mem (hstable P hP hy) (Z.val.smul_mem c (hP hx))
  have hz : y-c•x=0 := hnondeg _ hv (by
    intro w hw
    have hh := LinearMap.congr_fun he ⟨w,hw⟩
    change B y w=c*B x w at hh
    simp only [map_sub,map_smul,LinearMap.sub_apply,LinearMap.smul_apply,smul_eq_mul,hh,sub_self])
  have hyP : y∈P.val := (sub_eq_zero.mp hz) ▸ P.val.smul_mem c hx
  exact (point_eq_of_common_nonzero B P (f P) y hyP hy hy0).symm

end SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints
