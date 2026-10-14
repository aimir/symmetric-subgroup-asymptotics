import SymmetricSubgroupAsymptotics.Non2PreE7C2Wreath
import SymmetricSubgroupAsymptotics.NormalGeneratorExtension
import SymmetricSubgroupAsymptotics.CyclicQuotientSocles

/-! A symmetric pairing identifies a subgroup of a product with either
coordinate projection. Adjoining coordinate exchange gives a complement
whose normal-generator bound is the local bound plus one. The pairing
need not be presented through matrices or a named classical group. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PairedFormSwapComplement

open SemidirectProduct

variable {R X Y : Type} [Group R]
variable (ρ : R →* Equiv.Perm X) (B : X → X → Y)

def graph : Subgroup (R × R) where
  carrier := {g | ∀ x y, B (ρ g.1 x) (ρ g.2 y) = B x y}
  one_mem' := by intro x y; simp
  mul_mem' := by
    intro g h hg hh x y
    change B (ρ (g.1 * h.1) x) (ρ (g.2 * h.2) y) = B x y
    rw [map_mul, map_mul]
    exact (hg (ρ h.1 x) (ρ h.2 y)).trans (hh x y)
  inv_mem' := by
    intro g hg x y
    have h := hg ((ρ g.1)⁻¹ x) ((ρ g.2)⁻¹ y)
    change B (ρ g.1⁻¹ x) (ρ g.2⁻¹ y) = B x y
    simpa only [map_inv, Equiv.Perm.inv_def, Equiv.apply_symm_apply] using h.symm

def first : graph ρ B →* R := (MonoidHom.fst R R).comp (graph ρ B).subtype

theorem first_injective (hρ : Function.Injective ρ)
    (hsep : ∀ u v : X, (∀ x, B x u = B x v) → u = v) :
    Function.Injective (first ρ B) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hfirst : g.val.1 = 1 := hg
  have hsecond : ρ g.val.2 = 1 := by
    apply Equiv.ext
    intro y
    apply hsep
    intro x
    simpa only [hfirst, map_one, Equiv.Perm.one_apply] using g.property x y
  apply Subtype.ext
  exact Prod.ext hfirst (hρ (hsecond.trans ρ.map_one.symm))

def firstEquiv (hρ : Function.Injective ρ)
    (hsep : ∀ u v : X, (∀ x, B x u = B x v) → u = v)
    (hsurj : Function.Surjective (first ρ B)) : graph ρ B ≃* R :=
  MulEquiv.ofBijective (first ρ B) ⟨first_injective ρ B hρ hsep, hsurj⟩

theorem first_surjective_of_generators {ι : Type} (g : ι → R)
    (hgen : Subgroup.closure (Set.range g) = ⊤)
    (hpairs : ∀ i, ∃ h : R, (g i, h) ∈ graph ρ B) :
    Function.Surjective (first ρ B) := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← hgen]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  obtain ⟨h, hh⟩ := hpairs i
  exact ⟨⟨(g i, h), hh⟩, rfl⟩

variable (hsymm : ∀ x y, B x y = B y x)

include hsymm in
theorem swapped_mem (g : graph ρ B) : (g.val.2, g.val.1) ∈ graph ρ B := by
  intro x y
  calc
    B (ρ g.val.2 x) (ρ g.val.1 y) = B (ρ g.val.1 y) (ρ g.val.2 x) := hsymm _ _
    _ = B y x := g.property y x
    _ = B x y := hsymm _ _

def swap : MulAut (graph ρ B) where
  toFun g := ⟨(g.val.2, g.val.1), swapped_mem ρ B hsymm g⟩
  invFun g := ⟨(g.val.2, g.val.1), swapped_mem ρ B hsymm g⟩
  left_inv g := by apply Subtype.ext; rfl
  right_inv g := by apply Subtype.ext; rfl
  map_mul' g h := by apply Subtype.ext; rfl

def swapAction : Multiplicative (ZMod 2) →* MulAut (graph ρ B) where
  toFun c := if c = 1 then 1 else swap ρ B hsymm
  map_one' := if_pos rfl
  map_mul' c d := by
    rcases C2Wreath.cases c with rfl | rfl <;>
      rcases C2Wreath.cases d with rfl | rfl
    · simp
    · simp [C2Wreath.gen_ne_one]
    · simp [C2Wreath.gen_ne_one]
    · rw [C2Wreath.gen_mul_gen, if_pos rfl, if_neg C2Wreath.gen_ne_one]
      apply MulEquiv.ext
      intro g
      apply Subtype.ext
      rfl

abbrev Model := graph ρ B ⋊[swapAction ρ B hsymm] Multiplicative (ZMod 2)

def intoWreath : Model ρ B hsymm →* C2Wreath.W R :=
  SemidirectProduct.map (graph ρ B).subtype (MonoidHom.id _)
    (by
      intro c
      rcases C2Wreath.cases c with rfl | rfl
      · apply MonoidHom.ext
        intro g
        change ((swapAction ρ B hsymm 1) g).val = C2Wreath.swapAut R 1 g.val
        rw [(swapAction ρ B hsymm).map_one, C2Wreath.swapAut_one]
        rfl
      · apply MonoidHom.ext
        intro g
        change ((swapAction ρ B hsymm C2Wreath.gen) g).val =
          C2Wreath.swapAut R C2Wreath.gen g.val
        change (swap ρ B hsymm g).val = (g.val.2, g.val.1)
        rfl
    )

theorem intoWreath_injective : Function.Injective (intoWreath ρ B hsymm) := by
  intro g h heq
  apply SemidirectProduct.ext
  · apply Subtype.ext
    exact congrArg (fun z : C2Wreath.W R ↦ z.left) heq
  · exact congrArg (fun z : C2Wreath.W R ↦ z.right) heq

/-- The graph hypothesis is checked by literal generator pairs; no group
order or normal-subgroup catalogue is part of this result. -/
theorem normal_generating_tuples
    (hρ : Function.Injective ρ)
    (hsep : ∀ u v : X, (∀ x, B x u = B x v) → u = v)
    (hsurj : Function.Surjective (first ρ B)) {a : ℕ}
    (hR : ∀ N : Subgroup R, N.Normal →
      ∃ x : Fin a → R, Subgroup.normalClosure (Set.range x) = N) :
    ∀ N : Subgroup (Model ρ B hsymm), N.Normal →
      ∃ x : Fin (a + 1) → Model ρ B hsymm,
        Subgroup.normalClosure (Set.range x) = N := by
  let π : Model ρ B hsymm →* Multiplicative (ZMod 2) := rightHom
  let e : graph ρ B ≃* π.ker :=
    (MonoidHom.ofInjective (f := (inl : graph ρ B →* Model ρ B hsymm))
      inl_injective).trans (MulEquiv.subgroupCongr range_inl_eq_ker_rightHom)
  let f : R ≃* π.ker := (firstEquiv ρ B hρ hsep hsurj).symm.trans e
  exact normal_generating_tuples_of_kernel_and_image π rightHom_surjective
    (normal_generating_tuples_of_surjective f.toMonoidHom f.surjective hR)
    normal_generating_singletons_of_isCyclic

end PairedFormSwapComplement
end SymmetricSubgroupAsymptotics

end
