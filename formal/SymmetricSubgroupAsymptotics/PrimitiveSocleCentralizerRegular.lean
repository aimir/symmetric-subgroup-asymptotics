import SymmetricSubgroupAsymptotics.PrimitiveSocleAffineAlternative
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Order.Preorder.Finite

/-! Centralizers of actual transitive subgroups are semiregular. This gives
the two-regular-minimal-normal branch of the full primitive socle theorem. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleONanScottHelpers

variable {G X : Type} [Group G] [MulAction G X] [FaithfulSMul G X]

/-- Commutation with a transitive subgroup forces any point-fixing element
to be the identity in the original faithful action. -/
theorem free_of_commuting_transitive (H K : Subgroup G)
    [MulAction.IsPretransitive K X]
    (hcomm : ∀ h : H, ∀ k : K, Commute (h : G) (k : G))
    (x : X) (h : H) (hfix : h • x=x) : h=1 := by
  apply Subtype.ext
  apply FaithfulSMul.eq_of_smul_eq_smul (α := X)
  intro y
  obtain ⟨k,hk⟩ := MulAction.exists_smul_eq K x y
  change (h : G) • x=x at hfix
  change (k : G) • x=y at hk
  calc
    (h : G) • y = (h : G) • ((k : G) • x) := by rw [hk]
    _ = (k : G) • ((h : G) • x) := by rw [←mul_smul,(hcomm h k).eq,mul_smul]
    _ = y := by rw [hfix,hk]
    _ = (1 : G) • y := (one_smul G y).symm

/-- The actual centralizer of a transitive subgroup acts freely. -/
theorem centralizer_free (H : Subgroup G)
    [MulAction.IsPretransitive H X]
    (x : X) (c : Subgroup.centralizer (H : Set G)) (hc : c • x=x) : c=1 := by
  apply free_of_commuting_transitive (Subgroup.centralizer (H : Set G)) H ?_ x c hc
  intro c h
  exact (Subgroup.mem_centralizer_iff.mp c.property (h : G) h.property).symm

omit [FaithfulSMul G X] in
/-- Transitivity and this literal freeness statement give regularity. -/
theorem regular_of_free (H : Subgroup G) [MulAction.IsPretransitive H X]
    (hfree : ∀ (x : X) (h : H), h • x=x → h=1) :
    ∀ x y : X, ∃! h : H, h • x=y := by
  intro x y
  obtain ⟨h,hh⟩ := MulAction.exists_smul_eq H x y
  refine ⟨h,hh,?_⟩
  intro k hk
  have he : h⁻¹*k=1 := hfree x _ (by rw [mul_smul,hk,←hh,inv_smul_smul])
  exact (inv_mul_eq_one.mp he).symm

/-- Evaluation coordinates on the same original points for any regular
subgroup, without an abstract replacement action. -/
def regularPointEquiv (H : Subgroup G)
    (hregular : ∀ x y : X, ∃! h : H, h • x=y) (x : X) : H ≃ X where
  toFun h := h • x
  invFun y := Classical.choose (hregular x y)
  left_inv h := ((Classical.choose_spec (hregular x (h • x))).2 h rfl).symm
  right_inv y := (Classical.choose_spec (hregular x y)).1

/-- Two commuting regular subgroups are isomorphic by inverse evaluation.
The inverse is essential for multiplication order in a nonabelian group. -/
def commutingRegularEquiv (H K : Subgroup G)
    (hH : ∀ x y : X, ∃! h : H, h • x=y)
    (hK : ∀ x y : X, ∃! k : K, k • x=y)
    (hcomm : ∀ h : H, ∀ k : K, Commute (h : G) (k : G)) (x : X) : H ≃* K := by
  let eH := regularPointEquiv H hH x
  let eK := regularPointEquiv K hK x
  let e : H ≃ K := (Equiv.inv H).trans (eH.trans eK.symm)
  have he (h : H) : e h • x = h⁻¹ • x := eK.apply_symm_apply _
  exact {
    toEquiv := e
    map_mul' := by
      intro h k
      apply eK.injective
      change e (h*k) • x = (e h * e k) • x
      rw [he,mul_inv_rev,mul_smul]
      calc
        k⁻¹ • (h⁻¹ • x) = k⁻¹ • (e h • x) := by rw [he]
        _ = e h • (k⁻¹ • x) := by
          change ((k⁻¹ : H) : G) • (((e h : K) : G) • x) =
            ((e h : K) : G) • (((k⁻¹ : H) : G) • x)
          rw [←mul_smul,(hcomm k⁻¹ (e h)).eq,mul_smul]
        _ = e h • (e k • x) := by rw [he]
        _ = (e h * e k) • x := (mul_smul _ _ _).symm }

/-- A regular normal subgroup of a faithful primitive group is minimal
normal. Every nontrivial normal subgroup inside it is transitive. -/
theorem regular_normal_minimal [MulAction.IsPreprimitive G X] [Nonempty X]
    (H : Subgroup G) [H.Normal] (hne : H≠⊥)
    (hregular : ∀ x y : X, ∃! h : H, h • x=y) : IsMinimalNormalSubgroup H := by
  refine ⟨inferInstance,hne,?_⟩
  intro K hK hKne hKH
  letI : K.Normal := hK
  letI : MulAction.IsPretransitive K X := normal_transitive_of_ne_bot K hKne
  apply le_antisymm hKH
  intro h hh
  let x : X := Classical.choice inferInstance
  obtain ⟨k,hk⟩ := MulAction.exists_smul_eq K x ((⟨h,hh⟩ : H) • x)
  have he : (⟨(k : G),hKH k.property⟩ : H)=⟨h,hh⟩ := by
    exact ((Classical.choose_spec (hregular x ((⟨h,hh⟩ : H) • x))).2 _ hk).trans
      ((Classical.choose_spec (hregular x ((⟨h,hh⟩ : H) • x))).2 _ rfl).symm
  have hv : (k : G)=h := congrArg Subtype.val he
  exact hv ▸ k.property

/-- An actual minimal normal subgroup exists in every finite nontrivial
group, by minimization in the original normal-subgroup lattice. -/
theorem exists_minimalNormal [Finite G] [Nontrivial G] :
    ∃ E : Subgroup G, IsMinimalNormalSubgroup E := by
  let good : Subgroup G → Prop := fun E => E.Normal ∧ E≠⊥
  obtain ⟨E,_,hE⟩ := Finite.exists_le_minimal (p := good) (a := (⊤ : Subgroup G))
    ⟨inferInstance,top_ne_bot⟩
  refine ⟨E,⟨hE.1.1,hE.1.2,?_⟩⟩
  intro K hK hKne hKE
  exact hE.eq_of_le ⟨hK,hKne⟩ hKE

end SymmetricSubgroupAsymptotics.PrimitiveSocleONanScottHelpers
