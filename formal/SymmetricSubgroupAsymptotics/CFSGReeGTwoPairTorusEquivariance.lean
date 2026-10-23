import SymmetricSubgroupAsymptotics.CFSGReeGTwoAlignedCentreAction
import SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveCentralQuotient

/-! If an actual opposed-pair automorphism fixes the central axis,
it fixes every actual squared torus word. Its restriction to U therefore
commutes with the same squared torus action used by intrinsic rigidity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoPairTorusEquivariance
open CFSGReeGTwoFieldParameters CFSGReeGTwoFixedModelEquivalence
open CFSGReeGTwoPairRestriction CFSGReeGTwoAlignedCentreAction
open CFSGReeGTwoPermutationDegree CFSGReeGTwoPositiveDerived
open CFSGReeGTwoOriginalPositiveSubgroup CFSGReeGTwoPositiveCentralQuotient
open CFSGReeGTwoOriginalTorus

theorem pair_central_fixed (m : ℕ) (hm : 1≤m) (f : pairStabilizer m hm)
    (hf : alignedCentreAction m hm f=1) (d : Field m) :
    f.val (centralDerivedHom m hm (Multiplicative.ofAdd d))=
      centralDerivedHom m hm (Multiplicative.ofAdd d) := by
  rw [pair_central_intertwine,hf]
  rfl

theorem pair_fixes_square_torus (m : ℕ) (hm : 1≤m) (f : pairStabilizer m hm)
    (hf : alignedCentreAction m hm f=1) (r : (Field m)ˣ) :
    f.val (squareTorusDerived m r)=squareTorusDerived m r := by
  obtain ⟨v,hv⟩ := pair_maps_square_torus m hm f r
  have hh := congrArg f.val (squareTorusDerived_action m hm r 1)
  rw [map_mul,map_mul,map_inv,hv,pair_central_fixed m hm f hf,
    pair_central_fixed m hm f hf,squareTorusDerived_action,one_mul,one_mul] at hh
  have hval : (v:Field m)^2=(r:Field m)^2 :=
    congrArg Multiplicative.toAdd (centralDerivedHom_injective m hm hh)
  have he : v^2=r^2 := Units.ext hval
  calc
    _ = squareTorusDerived m v := hv
    _ = squareTorusDerived m r := by
      apply Subtype.ext
      exact congrArg (fixedTorusHom m) he

theorem pairRestriction_intertwine (m : ℕ) (hm : 1≤m) (f : pairStabilizer m hm)
    (u : fixedPositiveGroup m) :
    positiveDerivedHom m hm (pairRestriction m hm f u)=f.val (positiveDerivedHom m hm u) := by
  apply Subtype.ext
  exact pairRestriction_val m hm f u

theorem square_torus_intertwine (m : ℕ) (hm : 1≤m) (r : (Field m)ˣ)
    (u : fixedPositiveGroup m) :
    positiveDerivedHom m hm (fixedPositiveTorusAut m (r^2) u)=
      squareTorusDerived m r*positiveDerivedHom m hm u*(squareTorusDerived m r)⁻¹ := by
  apply Subtype.ext
  exact fixedPositiveTorusAut_val m (r^2) u

theorem pairRestriction_commutes_square_torus (m : ℕ) (hm : 1≤m)
    (f : pairStabilizer m hm) (hf : alignedCentreAction m hm f=1) (r : (Field m)ˣ) :
    pairRestriction m hm f*fixedPositiveTorusAut m (r^2)=
      fixedPositiveTorusAut m (r^2)*pairRestriction m hm f := by
  apply MulEquiv.ext
  intro u
  have hinj : Function.Injective (positiveDerivedHom m hm) := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun d:Derived m=>d.val) hab
  apply hinj
  change positiveDerivedHom m hm (pairRestriction m hm f (fixedPositiveTorusAut m (r^2) u))=
    positiveDerivedHom m hm (fixedPositiveTorusAut m (r^2) (pairRestriction m hm f u))
  calc
    _ = f.val (positiveDerivedHom m hm (fixedPositiveTorusAut m (r^2) u)) :=
      pairRestriction_intertwine m hm f _
    _ = f.val (squareTorusDerived m r*positiveDerivedHom m hm u*(squareTorusDerived m r)⁻¹) :=
      congrArg f.val (square_torus_intertwine m hm r u)
    _ = squareTorusDerived m r*f.val (positiveDerivedHom m hm u)*(squareTorusDerived m r)⁻¹ := by
      rw [map_mul,map_mul,map_inv,pair_fixes_square_torus m hm f hf]
    _ = squareTorusDerived m r*positiveDerivedHom m hm (pairRestriction m hm f u)*
        (squareTorusDerived m r)⁻¹ := by rw [pairRestriction_intertwine]
    _ = _ := (square_torus_intertwine m hm r _).symm

end SymmetricSubgroupAsymptotics.CFSGReeGTwoPairTorusEquivariance
