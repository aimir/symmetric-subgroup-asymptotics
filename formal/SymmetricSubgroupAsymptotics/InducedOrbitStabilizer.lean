import SymmetricSubgroupAsymptotics.InducedOrbitDecomposition

/-! The literal stabilizer and twisted fibre of an original induced
orbit. The support piece is identified with coinduction from that actual
stabilizer; its original fibre action is retained. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
variable {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
variable (H P : Subgroup G) (ρ : Representation k H V) (x : G)

def inducedOrbitStabilizer : Subgroup P :=
  (H.comap (MulAut.conj x).toMonoidHom).comap P.subtype

def inducedOrbitTwist : inducedOrbitStabilizer H P x →* H where
  toFun l := ⟨x*((l:P):G)*x⁻¹,l.2⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' l m := by apply Subtype.ext; change x*(_*_)*x⁻¹=(x*_*x⁻¹)*(x*_*x⁻¹); group

abbrev inducedOrbitFibre : Representation k (inducedOrbitStabilizer H P x) V :=
  ρ.comp (inducedOrbitTwist H P x)

/-- Restriction to xP gives the actual twisted stabilizer-coinduced
function, not an untwisted permutation module. -/
def inducedOrbitRestrict :
    (coinducedOrbitPiece H P ρ (DoubleCoset.mk H P x)).toSubmodule →ₗ[k]
      Representation.coindV (inducedOrbitStabilizer H P x).subtype
        (inducedOrbitFibre H P ρ x) where
  toFun f := ⟨fun p => f.1.1 (x*(p:G)),by
    intro l p
    change f.1.1 (x*(((l:P):G)*(p:G)))=
      ρ (inducedOrbitTwist H P x l) (f.1.1 (x*(p:G)))
    rw [← f.1.2 (inducedOrbitTwist H P x l) (x*(p:G))]
    apply congrArg f.1.1
    change x*(_*_)=(x*_*x⁻¹)*(x*_)
    group⟩
  map_add' _ _ := by apply Subtype.ext; rfl
  map_smul' _ _ := by apply Subtype.ext; rfl

@[simp] theorem inducedOrbitRestrict_apply
    (f : (coinducedOrbitPiece H P ρ (DoubleCoset.mk H P x)).toSubmodule) (p : P) :
    (inducedOrbitRestrict H P ρ x f).1 p=f.1.1 (x*(p:G)) := rfl

theorem inducedOrbitRestrict_injective : Function.Injective (inducedOrbitRestrict H P ρ x) := by
  intro f f' he
  apply Subtype.ext
  apply Subtype.ext
  funext g
  by_cases hg : DoubleCoset.mk H P g=DoubleCoset.mk H P x
  · obtain ⟨h,hh,p,hp,hg'⟩ := (DoubleCoset.eq H P x g).mp hg.symm
    have hval := congrArg (fun u : Representation.coindV
      (inducedOrbitStabilizer H P x).subtype (inducedOrbitFibre H P ρ x) => u.1 ⟨p,hp⟩) he
    change f.1.1 (x*p)=f'.1.1 (x*p) at hval
    rw [hg',mul_assoc]
    exact (f.1.2 ⟨h,hh⟩ (x*p)).trans ((congrArg (ρ ⟨h,hh⟩) hval).trans
      (f'.1.2 ⟨h,hh⟩ (x*p)).symm)
  · rw [f.2 g hg,f'.2 g hg]

theorem inducedOrbitRestrict_equivariant (p : P)
    (f : (coinducedOrbitPiece H P ρ (DoubleCoset.mk H P x)).toSubmodule) :
    inducedOrbitRestrict H P ρ x
      ((coinducedOrbitPiece H P ρ (DoubleCoset.mk H P x)).toRepresentation p f)=
      Representation.coind (inducedOrbitStabilizer H P x).subtype
        (inducedOrbitFibre H P ρ x) p (inducedOrbitRestrict H P ρ x f) := by
  apply Subtype.ext
  funext z
  change f.1.1 ((x*(z:G))*(p:G))=f.1.1 (x*((z:G)*(p:G)))
  rw [mul_assoc]

/-- The value used to extend a stabilizer-equivariant function does not
depend on a chosen H-times-x-times-P decomposition. -/
theorem inducedOrbit_extension_consistent
    (u : Representation.coindV (inducedOrbitStabilizer H P x).subtype
      (inducedOrbitFibre H P ρ x)) (h₁ h₂ : H) (p₁ p₂ : P)
    (he : (h₁:G)*x*(p₁:G)=(h₂:G)*x*(p₂:G)) :
    ρ h₁ (u.1 p₁)=ρ h₂ (u.1 p₂) := by
  have hc : x*((p₂:G)*(p₁:G)⁻¹)*x⁻¹=(h₂:G)⁻¹*(h₁:G) := by
    calc
      _=(h₂:G)⁻¹*((h₂:G)*x*(p₂:G))*(p₁:G)⁻¹*x⁻¹ := by group
      _=(h₂:G)⁻¹*((h₁:G)*x*(p₁:G))*(p₁:G)⁻¹*x⁻¹ := by rw [he]
      _=_ := by group
  let l : inducedOrbitStabilizer H P x := ⟨p₂*p₁⁻¹,by
    change x*((p₂:G)*(p₁:G)⁻¹)*x⁻¹∈H
    rw [hc]
    exact H.mul_mem (H.inv_mem h₂.2) h₁.2⟩
  have hu := u.2 l p₁
  have hu' : u.1 p₂=ρ (h₂⁻¹*h₁) (u.1 p₁) := by
    change u.1 ((p₂*p₁⁻¹)*p₁)=ρ (inducedOrbitTwist H P x l) (u.1 p₁) at hu
    have ht : inducedOrbitTwist H P x l=h₂⁻¹*h₁ := Subtype.ext hc
    simpa only [inv_mul_cancel_right,ht] using hu
  rw [hu',map_mul]
  change ρ h₁ (u.1 p₁)=((ρ h₂)*(ρ h₂⁻¹)*(ρ h₁)) (u.1 p₁)
  rw [← map_mul,mul_inv_cancel,map_one,one_mul]

theorem inducedOrbit_exists_decomposition (g : G)
    (hg : DoubleCoset.mk H P g=DoubleCoset.mk H P x) :
    ∃ z : H×P,g=(z.1:G)*x*(z.2:G) := by
  obtain ⟨h,hh,p,hp,he⟩ := (DoubleCoset.eq H P x g).mp hg.symm
  exact ⟨(⟨h,hh⟩,⟨p,hp⟩),he⟩

def inducedOrbitDecompositionChoice (g : G)
    (hg : DoubleCoset.mk H P g=DoubleCoset.mk H P x) : H×P :=
  Classical.choose (inducedOrbit_exists_decomposition H P x g hg)

theorem inducedOrbitDecompositionChoice_spec (g : G)
    (hg : DoubleCoset.mk H P g=DoubleCoset.mk H P x) :
    g=((inducedOrbitDecompositionChoice H P x g hg).1:G)*x*
      ((inducedOrbitDecompositionChoice H P x g hg).2:G) :=
  Classical.choose_spec (inducedOrbit_exists_decomposition H P x g hg)

/-- Extension by zero to the original G, using the original H-action
inside the supported double coset. -/
def inducedOrbitExtendFun
    (u : Representation.coindV (inducedOrbitStabilizer H P x).subtype
      (inducedOrbitFibre H P ρ x)) (g : G) : V :=
  if hg : DoubleCoset.mk H P g=DoubleCoset.mk H P x then
    ρ (inducedOrbitDecompositionChoice H P x g hg).1
      (u.1 (inducedOrbitDecompositionChoice H P x g hg).2)
  else 0

theorem inducedOrbitExtendFun_apply
    (u : Representation.coindV (inducedOrbitStabilizer H P x).subtype
      (inducedOrbitFibre H P ρ x)) (h : H) (p : P) :
    inducedOrbitExtendFun H P ρ x u ((h:G)*x*(p:G))=ρ h (u.1 p) := by
  have hg : DoubleCoset.mk H P ((h:G)*x*(p:G))=DoubleCoset.mk H P x := by
    rw [inducedOrbitLabel_right,inducedOrbitLabel_left]
  rw [inducedOrbitExtendFun,dif_pos hg]
  apply inducedOrbit_extension_consistent
  exact (inducedOrbitDecompositionChoice_spec H P x _ hg).symm

def inducedOrbitExtend
    (u : Representation.coindV (inducedOrbitStabilizer H P x).subtype
      (inducedOrbitFibre H P ρ x)) :
    (coinducedOrbitPiece H P ρ (DoubleCoset.mk H P x)).toSubmodule :=
  ⟨⟨inducedOrbitExtendFun H P ρ x u,by
    intro h g
    change inducedOrbitExtendFun H P ρ x u ((h:G)*g)=
      ρ h (inducedOrbitExtendFun H P ρ x u g)
    by_cases hg : DoubleCoset.mk H P g=DoubleCoset.mk H P x
    · obtain ⟨⟨h',p⟩,rfl⟩ := inducedOrbit_exists_decomposition H P x g hg
      dsimp only [Prod.fst,Prod.snd]
      have he : (h:G)*((h':G)*x*(p:G))=((h*h':H):G)*x*(p:G) := by simp [mul_assoc]
      rw [he,inducedOrbitExtendFun_apply,inducedOrbitExtendFun_apply,map_mul]
      rfl
    · have hg' : DoubleCoset.mk H P ((h:G)*g)≠DoubleCoset.mk H P x := by
        simpa only [inducedOrbitLabel_left] using hg
      simp only [inducedOrbitExtendFun,dif_neg hg,dif_neg hg',map_zero]⟩,by
    intro g hg
    exact dif_neg hg⟩

theorem inducedOrbitRestrict_extend
    (u : Representation.coindV (inducedOrbitStabilizer H P x).subtype
      (inducedOrbitFibre H P ρ x)) :
    inducedOrbitRestrict H P ρ x (inducedOrbitExtend H P ρ x u)=u := by
  apply Subtype.ext
  funext p
  change inducedOrbitExtendFun H P ρ x u (x*(p:G))=u.1 p
  have he := inducedOrbitExtendFun_apply H P ρ x u 1 p
  simpa using he

def inducedOrbitStabilizerEquiv :
    (coinducedOrbitPiece H P ρ (DoubleCoset.mk H P x)).toRepresentation.Equiv
      (Representation.coind (inducedOrbitStabilizer H P x).subtype
        (inducedOrbitFibre H P ρ x)) :=
  Representation.Equiv.mk
    (LinearEquiv.ofBijective (inducedOrbitRestrict H P ρ x)
      ⟨inducedOrbitRestrict_injective H P ρ x,
        fun u => ⟨inducedOrbitExtend H P ρ x u,inducedOrbitRestrict_extend H P ρ x u⟩⟩)
    (fun p => by apply LinearMap.ext; intro f; exact inducedOrbitRestrict_equivariant H P ρ x p f)

/-- Each actual support piece is the induction of its literal twisted
fibre from its literal original stabilizer. -/
def inducedOrbitPieceInductionEquiv [(inducedOrbitStabilizer H P x).FiniteIndex] :
    (coinducedOrbitPiece H P ρ (DoubleCoset.mk H P x)).toRepresentation.Equiv
      (Representation.ind (inducedOrbitStabilizer H P x).subtype
        (inducedOrbitFibre H P ρ x)) :=
  (inducedOrbitStabilizerEquiv H P ρ x).trans
    (inducedToCoinducedEquiv (inducedOrbitStabilizer H P x)
      (inducedOrbitFibre H P ρ x)).symm

end SymmetricSubgroupAsymptotics
