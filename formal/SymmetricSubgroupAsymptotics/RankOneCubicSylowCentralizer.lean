import SymmetricSubgroupAsymptotics.SylowEpimorphismRestriction
import SymmetricSubgroupAsymptotics.BinaryRegularKleinWreathCoordinates
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Algebra.CharP.Two

/-! Actual Sylow and conjugation-kernel bridge for a normal cubic line.
The block-kernel injectivity input is precisely the structural endpoint
of the monomial subquotient lemma, not a normal-generator bound. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.RankOneCubicSylowCentralizer

abbrev Cubic := Multiplicative (ZMod 3)
abbrev Blocks := BinaryRegularKleinWreath.R

private theorem blocks_square (r : Blocks) : r^2=1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow]
  change (2 : ℕ) • r.toAdd=0
  rw [two_nsmul]
  funext i
  change r.toAdd i+r.toAdd i=0
  exact CharTwo.add_self_eq_zero _

def cubicGenerator : Cubic := Multiplicative.ofAdd 1

private theorem cubic_cover : ∀ z : Cubic, ∃ n : Fin 3, cubicGenerator^n.val=z := by
  decide +kernel

/-- Automorphisms of an actual cubic line are determined by the image of
one actual generator, which has only two nonidentity possibilities. -/
theorem automorphism_card_le_two {K : Type} [Group K] (e : K ≃* Cubic) :
    Nat.card (MulAut K)≤2 := by
  let u := e.symm cubicGenerator
  have hu : u≠1 := by
    intro h
    have he := congrArg e h
    have hn : cubicGenerator≠1 := by decide +kernel
    exact hn (by simpa only [u,MulEquiv.apply_symm_apply,map_one] using he)
  let eval : MulAut K → {z : Cubic // z≠1} := fun f =>
    ⟨e (f u),by
      intro h
      have hf : f u=1 := e.injective (by simpa only [map_one] using h)
      exact hu (f.injective (by simpa only [map_one] using hf))⟩
  have hinj : Function.Injective eval := by
    intro f g he
    have hfg : f u=g u := e.injective (congrArg Subtype.val he)
    apply MulEquiv.ext
    intro x
    obtain ⟨n,hn⟩ := cubic_cover (e x)
    have hx : x=u^n.val := by
      apply e.injective
      simpa only [u,map_pow,MulEquiv.apply_symm_apply] using hn.symm
    rw [hx,map_pow,map_pow,hfg]
  letI : Finite (MulAut K) := Finite.of_injective eval hinj
  have hcard : Nat.card {z : Cubic // z≠1}=2 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  exact (Nat.card_le_card_of_injective eval hinj).trans_eq hcard

/-- The actual Sylow action on the cubic line has a nonidentity kernel
when it maps onto the four-point regular block group. -/
theorem sylow_conjugation_kernel_nontrivial
    {G : Type} [Group G] [Finite G]
    (O : Subgroup G) [O.Normal] (e : O ≃* Cubic)
    (top : G →* Blocks) (htop : Function.Surjective top) (P : Sylow 2 G) :
    ((MulAut.conjNormal : G →* MulAut O).comp (P : Subgroup G).subtype).ker≠⊥ := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  let a := (MulAut.conjNormal : G →* MulAut O).comp (P : Subgroup G).subtype
  have hR : IsPGroup 2 Blocks := by
    intro r
    refine ⟨1,?_⟩
    exact blocks_square r
  have hsurj := sylow_restrict_surjective P hR top htop
  have hfour : Nat.card Blocks=4 := by
    rw [Nat.card_congr Multiplicative.toAdd,Nat.card_fun,Nat.card_fin,Nat.card_zmod]
    norm_num
  intro hbot
  have hinj : Function.Injective a := a.ker_eq_bot_iff.mp hbot
  have hsmall : Nat.card (P : Subgroup G)≤2 :=
    (Nat.card_le_card_of_injective a hinj).trans (automorphism_card_le_two e)
  have hlarge : 4≤Nat.card (P : Subgroup G) := by
    rw [← hfour]
    exact Nat.card_le_card_of_surjective _ hsurj
  omega

/-- Once the actual monomial action kernel injects into the actual block
image, the nonidentity conjugation kernel contains an ACTUAL involution.
No splitting of an original affine extension is used. -/
theorem exists_commuting_involution
    {G : Type} [Group G] [Finite G]
    (O : Subgroup G) [O.Normal] (e : O ≃* Cubic)
    (top : G →* Blocks) (htop : Function.Surjective top) (P : Sylow 2 G)
    (hinj : Function.Injective
      ((top.comp (P : Subgroup G).subtype).comp
        (((MulAut.conjNormal : G →* MulAut O).comp
          (P : Subgroup G).subtype).ker.subtype))) :
    ∃ s : G, s∈(P : Subgroup G) ∧ s^2=1 ∧ top s≠1 ∧
      ∀ o : O, Commute s (o : G) := by
  let a := (MulAut.conjNormal : G →* MulAut O).comp (P : Subgroup G).subtype
  have hne : a.ker≠⊥ := sylow_conjugation_kernel_nontrivial O e top htop P
  letI : Nontrivial a.ker := a.ker.nontrivial_iff_ne_bot.mpr hne
  obtain ⟨x,hx⟩ := exists_ne (1 : a.ker)
  have ht : top ((x : (P : Subgroup G)) : G)≠1 := by
    intro h
    apply hx
    apply hinj
    simpa only [MonoidHom.comp_apply,map_one] using h
  have hsq : x^2=1 := by
    apply hinj
    change top (((x : (P : Subgroup G)) : G)^2)=top 1
    rw [map_pow,map_one]
    exact blocks_square _
  refine ⟨((x : (P : Subgroup G)) : G),(x : (P : Subgroup G)).property,
    congrArg (fun z : a.ker => ((z : (P : Subgroup G)) : G)) hsq,ht,?_⟩
  intro o
  have ha : a (x : (P : Subgroup G))=1 := x.property
  have hc := congrArg (fun f : MulAut O => (f o : G)) ha
  change ((x : (P : Subgroup G)) : G)*(o : G)*
    ((x : (P : Subgroup G)) : G)⁻¹=(o : G) at hc
  exact mul_inv_eq_iff_eq_mul.mp hc

end SymmetricSubgroupAsymptotics.RankOneCubicSylowCentralizer
