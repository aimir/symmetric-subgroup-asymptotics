import SymmetricSubgroupAsymptotics.ScalarFourCentralC4TopCoordinates
import SymmetricSubgroupAsymptotics.EpimorphismKernelLabels
import Mathlib.Logic.Equiv.Sum

/-! Literal maps over one actual finite top. All top-section evaluations
are retained, and each remaining fibre uses the nonsplit central/active
restriction bound. The sum over different top maps is not discarded. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.ScalarFourCentralC4TopCoordinates
variable {Q T J : Type} [Group Q] [Group T] [Group J]
  [Finite Q] [Finite T] [Finite J] {c d : ℕ}
  (D : ScalarFourCentralC4TopCoordinates Q T c d)

abbrev TopFibre (theta : J →* T) :=
  {phi : GroupEpimorphism J Q // D.top.comp phi.val=theta}

private theorem card_le_fibres {X Y : Type} [Finite X] [Fintype Y]
    (f : X → Y) (m : ℕ) (hm : ∀ y : Y, Nat.card {x : X // f x = y} ≤ m) :
    Nat.card X≤Nat.card Y*m := by
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f),Nat.card_sigma]
  exact (Finset.sum_le_sum (fun y _ => hm y)).trans_eq (by simp [Nat.card_eq_fintype_card])

/-- The coefficient is fixed by the target; no top-map multiplicity has
been absorbed into it. -/
theorem fixed_top_card_le (theta : J →* T) (htheta : Function.Surjective theta) :
    Nat.card (D.TopFibre theta) ≤
      Nat.card Q ^ Nat.card T * Nat.card (theta.ker →* InvariantC4Scalar)^(max c d) := by
  choose s hs using htheta
  let F := theta.ker
  let L := D.TopFibre theta
  let restrict : L → (F →* D.top.ker) := fun phi =>
    (phi.val.val.comp F.subtype).codRestrict D.top.ker (by
      intro f
      change D.top (phi.val.val (f : J))=1
      have he := DFunLike.congr_fun phi.property (f : J)
      change D.top (phi.val.val (f : J))=theta (f : J) at he
      exact he.trans f.property)
  let eval : L → T → Q := fun phi t => phi.val.val (s t)
  have hdet (phi chi : L) (he : eval phi=eval chi)
      (hr : restrict phi=restrict chi) : phi=chi := by
    apply Subtype.ext
    apply Subtype.ext
    apply MonoidHom.ext
    intro g
    let t := theta g
    have hm : (s t)⁻¹*g ∈ F := by
      change theta ((s t)⁻¹*g)=1
      rw [map_mul,map_inv,hs]
      exact inv_mul_cancel t
    have hf := congrArg Subtype.val (DFunLike.congr_fun hr ⟨_,hm⟩)
    change phi.val.val ((s t)⁻¹*g)=chi.val.val ((s t)⁻¹*g) at hf
    have hv := congrFun he t
    change phi.val.val (s t)=chi.val.val (s t) at hv
    rw [map_mul,map_inv,map_mul,map_inv,hv] at hf
    exact mul_left_cancel hf
  letI : Finite (J →* Q) := Finite.of_injective
    (fun f : J →* Q => (f : J → Q)) DFunLike.coe_injective
  letI : Finite (F →* D.top.ker) := Finite.of_injective
    (fun f : F →* D.top.ker => (f : F → D.top.ker)) DFunLike.coe_injective
  letI : Fintype (T → Q) := Fintype.ofFinite _
  have hfibre (e : T → Q) :
      Nat.card {phi : L // eval phi=e} ≤
        Nat.card (F →* InvariantC4Scalar)^(max c d) := by
    by_cases hn : Nonempty {phi : L // eval phi=e}
    · obtain ⟨phi₀⟩ := hn
      have hv : D.top (e D.cubic)=D.cubic := by
        have he := congrFun phi₀.property D.cubic
        have htop := DFunLike.congr_fun phi₀.val.property (s D.cubic)
        change D.top (phi₀.val.val.val (s D.cubic))=theta (s D.cubic) at htop
        change phi₀.val.val.val (s D.cubic)=e D.cubic at he
        rw [he,hs] at htop
        exact htop
      let alpha : F → F := MulAut.conjNormal (s D.cubic)
      let beta : D.top.ker ≃* D.top.ker := MulAut.conjNormal (e D.cubic)
      let enc : {phi : L // eval phi=e} →
          ActualCentralC4ActiveRestrictionCount.Restriction alpha beta := fun phi =>
        ⟨restrict phi.val,by
          intro f
          apply Subtype.ext
          change phi.val.val.val (s D.cubic*(f : J)*(s D.cubic)⁻¹)=
            e D.cubic*phi.val.val.val (f : J)*(e D.cubic)⁻¹
          simp only [map_mul,map_inv]
          have he := congrFun phi.property D.cubic
          change phi.val.val.val (s D.cubic)=e D.cubic at he
          rw [he]⟩
      have hi : Function.Injective enc := by
        intro phi chi h
        apply Subtype.ext
        apply hdet
        · exact phi.property.trans chi.property.symm
        · exact congrArg Subtype.val h
      exact (Nat.card_le_card_of_injective enc hi).trans
        (D.restriction_card_le alpha (e D.cubic) hv)
    · letI : IsEmpty {phi : L // eval phi=e} := not_nonempty_iff.mp hn
      rw [Nat.card_of_isEmpty]
      exact Nat.zero_le _
  have h := card_le_fibres eval _ hfibre
  simpa only [Nat.card_fun] using h
end SymmetricSubgroupAsymptotics.ScalarFourCentralC4TopCoordinates
