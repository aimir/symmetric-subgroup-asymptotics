import SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveCommutatorSeeds
import SymmetricSubgroupAsymptotics.CFSGSquareScalarRigidity

/-! The actual c-image of U3-derived is the whole field. A literal
fixed-torus witness t=x*alpha(x) has c-weight x^2; the checked
odd-characteristic difference-of-squares theorem then fills the image.
No cyclic-field, gcd, rank or order assumption is needed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveDerivedMiddleImage
open CFSGReeGTwoFieldParameters CFSGReeGTwoOriginalPositiveSubgroup
open CFSGReeGTwoPositiveCoordinates CFSGReeGTwoPositiveFirstQuotient
open CFSGReeGTwoPositiveCommutatorSeeds CFSGReeGTwoOriginalTorus
open CFSGReeGTwoPositiveDerived CFSGReeGTwoFixedTorusAction
open CFSGReeGTwoOriginalFixedWordChart CFSGGTwoNaturalPositiveTorusAction

def derivedMiddleHom (m : ℕ) : commutator (fixedPositiveGroup m) →* Multiplicative (Field m) :=
  (middleHom m).comp (Subgroup.inclusion (commutator_le_firstKernel m))

def middleImage (m : ℕ) : AddSubgroup (Field m) := (derivedMiddleHom m).range.toAddSubgroup'

theorem mem_middleImage_iff (m : ℕ) (c : Field m) :
    c∈middleImage m ↔ ∃ u : fixedPositiveGroup m,
      u∈commutator (fixedPositiveGroup m) ∧ coordinates m u 1=c := by
  change Multiplicative.ofAdd c∈(derivedMiddleHom m).range ↔ _
  constructor
  · rintro ⟨u,he⟩
    refine ⟨u.val,u.property,?_⟩
    change Multiplicative.ofAdd (coordinates m u.val 1)=Multiplicative.ofAdd c at he
    exact congrArg (fun z : Multiplicative (Field m) => z.toAdd) he
  · rintro ⟨u,hu,hc⟩
    refine ⟨⟨u,hu⟩,?_⟩
    change Multiplicative.ofAdd (coordinates m u 1)=Multiplicative.ofAdd c
    rw [hc]

def middleWeight (m : ℕ) (t : (Field m)ˣ) : (Field m)ˣ := t⁻¹*unitsAlpha m t

theorem torus_coordinates (m : ℕ) (t : (Field m)ˣ) (u : fixedPositiveGroup m) :
    coordinates m (fixedPositiveTorusAut m t u)=fixedScaleCoordinates m t (coordinates m u) := by
  obtain ⟨x,rfl⟩ := fixedPositiveChart_surjective m u
  have he : fixedPositiveTorusAut m t (fixedPositiveChart m x)=
      fixedPositiveChart m (fixedScaleCoordinates m t x) := by
    apply Subtype.ext
    change fixedTorusHom m t*fixedWord m x*(fixedTorusHom m t)⁻¹=
      fixedWord m (fixedScaleCoordinates m t x)
    exact fixedTorus_fixedWord m t x
  rw [he,coordinates_chart,coordinates_chart]

theorem torus_middle (m : ℕ) (t : (Field m)ˣ) (u : fixedPositiveGroup m) :
    coordinates m (fixedPositiveTorusAut m t u) 1=
      coordinates m u 1*(middleWeight m t : Field m) := by
  rw [torus_coordinates]
  rfl

theorem middleWeight_square_witness (m : ℕ) (x : (Field m)ˣ) :
    middleWeight m (x*unitsAlpha m x)=x^2 := by
  have ha : unitsAlpha m (unitsAlpha m x)=x^3 := Units.ext (alpha_twice m (x : Field m))
  unfold middleWeight
  rw [map_mul,ha]
  calc
    (x*unitsAlpha m x)⁻¹*(unitsAlpha m x*x^3)=
        (unitsAlpha m x)⁻¹*(unitsAlpha m x*(x⁻¹*x^3)) := by rw [mul_inv_rev]; ac_rfl
    _ = x⁻¹*x^3 := inv_mul_cancel_left _ _
    _ = x^2 := by rw [pow_succ',inv_mul_cancel_left]

theorem torus_mem_commutator (m : ℕ) (t : (Field m)ˣ) (u : fixedPositiveGroup m)
    (hu : u∈commutator (fixedPositiveGroup m)) :
    fixedPositiveTorusAut m t u∈commutator (fixedPositiveGroup m) :=
  Subgroup.characteristic_iff_le_comap.mp
    (inferInstance : (commutator (fixedPositiveGroup m)).Characteristic) (fixedPositiveTorusAut m t) hu

theorem middleImage_square_stable (m : ℕ) (x c : Field m) (hc : c∈middleImage m) :
    x^2*c∈middleImage m := by
  by_cases hx : x=0
  · subst x
    simpa only [zero_pow (by decide : (2:ℕ)≠0),zero_mul] using (middleImage m).zero_mem
  · obtain ⟨u,hu,he⟩ := (mem_middleImage_iff m c).mp hc
    let xu : (Field m)ˣ := Units.mk0 x hx
    let t : (Field m)ˣ := xu*unitsAlpha m xu
    have hw : (middleWeight m t : Field m)=x^2 := by
      have hh := congrArg (fun z : (Field m)ˣ => (z : Field m)) (middleWeight_square_witness m xu)
      exact hh
    apply (mem_middleImage_iff m _).mpr
    refine ⟨fixedPositiveTorusAut m t u,torus_mem_commutator m t u hu,?_⟩
    rw [torus_middle,he,hw,mul_comm]

theorem middleImage_eq_top (m : ℕ) (hm : 1≤m) : middleImage m=⊤ := by
  obtain ⟨u,hu,hne⟩ := exists_nonzero_commutator_middle m hm
  have h2 : (2 : Field m)≠0 := (CharP.cast_eq_zero_iff (Field m) 3 2).not.mpr (by decide)
  exact CFSGSquareScalarRigidity.additive_subgroup_square_stable_eq_top h2 (middleImage m)
    (middleImage_square_stable m) (coordinates m u 1)
    ((mem_middleImage_iff m _).mpr ⟨u,hu,rfl⟩) hne

end SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveDerivedMiddleImage
