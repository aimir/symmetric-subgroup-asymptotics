import SymmetricSubgroupAsymptotics.InducedElementHead
import SymmetricSubgroupAsymptotics.PGroupInducedHead

/-!
# Descent of an injected coinduced representation through an onto group map

If the kernel of an onto map acts trivially on both a representation and
its inducing fibre, an injection into the original coinduced module descends
to an injection over the quotient image subgroup.  The construction uses
the actual onto map and proves independence of every chosen lift.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

variable {k G Q V U : Type} [Field k] [Group G] [Group Q]
    [AddCommGroup V] [Module k V] [AddCommGroup U] [Module k U]

/-- A representation killing the kernel of an onto map has the same value
on any two lifts of one quotient element. -/
theorem representation_apply_eq_of_map_eq (π : G →* Q)
    (τ : Representation k G U) (hτ : π.ker ≤ τ.ker)
    {x y : G} (hxy : π x = π y) : τ x = τ y := by
  have hdπ : x * y⁻¹ ∈ π.ker := by
    apply MonoidHom.mem_ker.mpr
    rw [map_mul, map_inv, hxy, mul_inv_cancel]
  have hdτ : τ (x * y⁻¹) = 1 := MonoidHom.mem_ker.mp (hτ hdπ)
  calc
    τ x = τ ((x * y⁻¹) * y) := by simp
    _ = τ (x * y⁻¹) * τ y := map_mul τ _ _
    _ = τ y := by rw [hdτ, one_mul]

/-- The representation on the quotient target obtained from an actual
surjective group map whose kernel acts trivially. -/
def representationDescend (π : G →* Q) (hπ : Function.Surjective π)
    (τ : Representation k G U) (hτ : π.ker ≤ τ.ker) :
    Representation k Q U where
  toFun q := τ (Function.surjInv hπ q)
  map_one' := by
    rw [← map_one τ]
    apply representation_apply_eq_of_map_eq π τ hτ
    simpa using Function.rightInverse_surjInv hπ (1 : Q)
  map_mul' q r := by
    rw [← map_mul τ]
    apply representation_apply_eq_of_map_eq π τ hτ
    calc
      π (Function.surjInv hπ (q * r)) = q * r :=
        Function.rightInverse_surjInv hπ (q * r)
      _ = π (Function.surjInv hπ q) * π (Function.surjInv hπ r) := by
        rw [Function.rightInverse_surjInv hπ, Function.rightInverse_surjInv hπ]
      _ = π (Function.surjInv hπ q * Function.surjInv hπ r) :=
        (map_mul π _ _).symm

@[simp]
theorem representationDescend_apply (π : G →* Q)
    (hπ : Function.Surjective π) (τ : Representation k G U)
    (hτ : π.ker ≤ τ.ker) (g : G) :
    representationDescend π hπ τ hτ (π g) = τ g := by
  apply representation_apply_eq_of_map_eq π τ hτ
  exact Function.rightInverse_surjInv hπ (π g)

variable (π : G →* Q) (hπ : Function.Surjective π)
    (H : Subgroup G) (ρ : Representation k H V)

abbrev subgroupImage : Subgroup Q := H.map π

abbrev subgroupImageMap : H →* subgroupImage π H := π.subgroupMap H

theorem subgroupImageMap_surjective :
    Function.Surjective (subgroupImageMap π H) :=
  MonoidHom.subgroupMap_surjective π H

/-- The inducing-fibre representation descended to the literal image of
the inducing subgroup. -/
def fibreRepresentationDescend
    (hρ : (subgroupImageMap π H).ker ≤ ρ.ker) :
    Representation k (subgroupImage π H) V :=
  representationDescend (subgroupImageMap π H)
    (subgroupImageMap_surjective π H) ρ hρ

@[simp]
theorem fibreRepresentationDescend_apply
    (hρ : (subgroupImageMap π H).ker ≤ ρ.ker) (h : H) :
    fibreRepresentationDescend π H ρ hρ (subgroupImageMap π H h) = ρ h := by
  exact representationDescend_apply (subgroupImageMap π H)
    (subgroupImageMap_surjective π H) ρ hρ h

/-- A coinduced function whose fibre action kills the quotient kernel has
equal values at any two original group elements with the same image. -/
theorem coinduced_apply_eq_of_map_eq
    (hK : π.ker ≤ H)
    (hρ : (subgroupImageMap π H).ker ≤ ρ.ker)
    (f : Representation.coindV H.subtype ρ)
    {x y : G} (hxy : π x = π y) : f.1 x = f.1 y := by
  have hdπ : x * y⁻¹ ∈ π.ker := by
    apply MonoidHom.mem_ker.mpr
    rw [map_mul, map_inv, hxy, mul_inv_cancel]
  have hdH : x * y⁻¹ ∈ H := by
    exact hK hdπ
  let d : H := ⟨x * y⁻¹, hdH⟩
  have hdβ : d ∈ (subgroupImageMap π H).ker := by
    apply MonoidHom.mem_ker.mpr
    apply Subtype.ext
    exact MonoidHom.mem_ker.mp hdπ
  have hρd : ρ d = 1 := MonoidHom.mem_ker.mp (hρ hdβ)
  have hf := f.2 d y
  change f.1 ((x * y⁻¹) * y) = ρ d (f.1 y) at hf
  simpa [hρd] using hf

/-- Descend one original coinduced function by evaluating it on chosen
lifts of quotient elements. -/
def coinducedFunctionDescend
    (hK : π.ker ≤ H)
    (hρ : (subgroupImageMap π H).ker ≤ ρ.ker)
    (f : Representation.coindV H.subtype ρ) :
    Representation.coindV (subgroupImage π H).subtype
      (fibreRepresentationDescend π H ρ hρ) := by
  let s : Q → G := Function.surjInv hπ
  have hs : Function.RightInverse s π := Function.rightInverse_surjInv hπ
  refine ⟨fun q => f.1 (s q), ?_⟩
  intro r q
  let β := subgroupImageMap π H
  let h : H := Function.surjInv (subgroupImageMap_surjective π H) r
  have hh : β h = r :=
    Function.rightInverse_surjInv (subgroupImageMap_surjective π H) r
  have hmap : π (s ((r : Q) * q)) = π ((h : G) * s q) := by
    rw [hs, map_mul, hs]
    exact congrArg (fun z : Q => z * q)
      (congrArg (fun z : subgroupImage π H => (z : Q)) hh).symm
  change f.1 (s ((r : Q) * q)) =
    fibreRepresentationDescend π H ρ hρ r (f.1 (s q))
  rw [coinduced_apply_eq_of_map_eq π H ρ hK hρ f hmap]
  have hf := f.2 h (s q)
  change f.1 ((h : G) * s q) = ρ h (f.1 (s q)) at hf
  rw [hf]
  have hrho := fibreRepresentationDescend_apply π H ρ hρ h
  rw [← hrho, hh]

/-- The quotient-descended coinduced function depends linearly on the
original one. -/
def coinducedFunctionDescendLinear
    (hK : π.ker ≤ H)
    (hρ : (subgroupImageMap π H).ker ≤ ρ.ker) :
    Representation.coindV H.subtype ρ →ₗ[k]
      Representation.coindV (subgroupImage π H).subtype
        (fibreRepresentationDescend π H ρ hρ) where
  toFun := coinducedFunctionDescend π hπ H ρ hK hρ
  map_add' _ _ := by
    apply Subtype.ext
    funext q
    simp [coinducedFunctionDescend]
  map_smul' _ _ := by
    apply Subtype.ext
    funext q
    simp [coinducedFunctionDescend]

/-- Descend an arbitrary injected representation inside the original
coinduced module. -/
def coinducedIntertwinerDescend
    (τ : Representation k G U) (hτ : π.ker ≤ τ.ker)
    (hK : π.ker ≤ H)
    (hρ : (subgroupImageMap π H).ker ≤ ρ.ker)
    (φ : τ.IntertwiningMap (Representation.coind H.subtype ρ)) :
    (representationDescend π hπ τ hτ).IntertwiningMap
      (Representation.coind (subgroupImage π H).subtype
        (fibreRepresentationDescend π H ρ hρ)) where
  toLinearMap := (coinducedFunctionDescendLinear π hπ H ρ hK hρ).comp φ.toLinearMap
  isIntertwining' q := by
    apply LinearMap.ext
    intro u
    let s : Q → G := Function.surjInv hπ
    have hs : Function.RightInverse s π := Function.rightInverse_surjInv hπ
    apply Subtype.ext
    funext r
    change
      (φ (representationDescend π hπ τ hτ q u)).1 (s r) =
        (φ u).1 (s ((r : Q) * q))
    have hτq : representationDescend π hπ τ hτ q = τ (s q) := by
      calc
        representationDescend π hπ τ hτ q =
            representationDescend π hπ τ hτ (π (s q)) := by rw [hs q]
        _ = τ (s q) := representationDescend_apply π hπ τ hτ (s q)
    rw [hτq]
    have hφ := Representation.IntertwiningMap.isIntertwining _ _ φ (s q) u
    have hval := congrArg
      (fun f : Representation.coindV H.subtype ρ => f.1 (s r)) hφ
    change (φ (τ (s q) u)).1 (s r) = (φ u).1 (s r * s q) at hval
    rw [hval]
    apply coinduced_apply_eq_of_map_eq π H ρ hK hρ (φ u)
    rw [map_mul, hs, hs]
    exact (hs (r * q)).symm

theorem coinducedIntertwinerDescend_injective
    (τ : Representation k G U) (hτ : π.ker ≤ τ.ker)
    (hK : π.ker ≤ H)
    (hρ : (subgroupImageMap π H).ker ≤ ρ.ker)
    (φ : τ.IntertwiningMap (Representation.coind H.subtype ρ))
    (hφ : Function.Injective φ) :
    Function.Injective
      (coinducedIntertwinerDescend π hπ H ρ τ hτ hK hρ φ) := by
  intro u v huv
  apply hφ
  apply Subtype.ext
  funext g
  let s : Q → G := Function.surjInv hπ
  have hs : Function.RightInverse s π := Function.rightInverse_surjInv hπ
  calc
    (φ u).1 g = (φ u).1 (s (π g)) :=
      coinduced_apply_eq_of_map_eq π H ρ hK hρ (φ u) (hs (π g)).symm
    _ = (φ v).1 (s (π g)) := by
      have h := congrFun (congrArg Subtype.val huv) (π g)
      change (φ u).1 (s (π g)) = (φ v).1 (s (π g)) at h
      exact h
    _ = (φ v).1 g :=
      coinduced_apply_eq_of_map_eq π H ρ hK hρ (φ v) (hs (π g))



section HeadDescent

variable {k G Q U : Type} [Field k] [Group G] [Group Q]
    [AddCommGroup U] [Module k U]

/-- Invariant linear forms are unchanged when a kernel-trivial
representation is descended along an onto map. -/
def representationDescendHeadEquiv
    (π : G →* Q) (hπ : Function.Surjective π)
    (τ : Representation k G U) (hτ : π.ker ≤ τ.ker) :
    τ.IntertwiningMap (Representation.trivial k G k) ≃ₗ[k]
      (representationDescend π hπ τ hτ).IntertwiningMap
        (Representation.trivial k Q k) where
  toFun f := {
    toLinearMap := f.toLinearMap
    isIntertwining' q := by
      obtain ⟨g, rfl⟩ := hπ q
      apply LinearMap.ext
      intro u
      simpa only [representationDescend_apply] using
        Representation.IntertwiningMap.isIntertwining τ
          (Representation.trivial k G k) f g u }
  invFun f := {
    toLinearMap := f.toLinearMap
    isIntertwining' g := by
      apply LinearMap.ext
      intro u
      have hi := Representation.IntertwiningMap.isIntertwining
        (representationDescend π hπ τ hτ)
        (Representation.trivial k Q k) f (π g) u
      simpa only [representationDescend_apply] using hi }
  left_inv _ := by apply Representation.IntertwiningMap.ext; rfl
  right_inv _ := by apply Representation.IntertwiningMap.ext; rfl
  map_add' _ _ := by apply Representation.IntertwiningMap.ext; rfl
  map_smul' _ _ := by apply Representation.IntertwiningMap.ext; rfl

theorem representationDescend_head_finrank_eq
    (π : G →* Q) (hπ : Function.Surjective π)
    (τ : Representation k G U) (hτ : π.ker ≤ τ.ker) :
    Module.finrank k
      ((representationDescend π hπ τ hτ).IntertwiningMap
        (Representation.trivial k Q k)) =
    Module.finrank k
      (τ.IntertwiningMap (Representation.trivial k G k)) :=
  (representationDescendHeadEquiv π hπ τ hτ).finrank_eq.symm

end HeadDescent

section EvaluationImage

variable {k G Q V U : Type} [Field k] [Group G] [Group Q]
    [AddCommGroup V] [Module k V] [AddCommGroup U] [Module k U]

/-- Evaluation at the identity in the original coinduced function model. -/
def coinducedIdentityEval (H : Subgroup G) (ρ : Representation k H V) :
    Representation.coindV H.subtype ρ →ₗ[k] V where
  toFun f := f.1 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The literal fibre subrepresentation reached by evaluating the injected
coinduced layer at the identity. -/
def intertwinerEvaluationImage
    (H : Subgroup G) (ρ : Representation k H V)
    (τ : Representation k G U)
    (φ : τ.IntertwiningMap (Representation.coind H.subtype ρ)) :
    Subrepresentation ρ where
  toSubmodule := LinearMap.range ((coinducedIdentityEval H ρ).comp φ.toLinearMap)
  apply_mem_toSubmodule h := by
    rintro _ ⟨u, rfl⟩
    refine ⟨τ (h : G) u, ?_⟩
    have hi := Representation.IntertwiningMap.isIntertwining τ
      (Representation.coind H.subtype ρ) φ (h : G) u
    have hi1 := congrArg
      (fun f : Representation.coindV H.subtype ρ => f.1 1) hi
    change (φ (τ (h : G) u)).1 1 = (φ u).1 (1 * (h : G)) at hi1
    simp only [one_mul] at hi1
    have hf := (φ u).2 h 1
    change (φ u).1 ((h : G) * 1) = ρ h ((φ u).1 1) at hf
    simp only [mul_one] at hf
    change (φ (τ (h : G) u)).1 1 = ρ h ((φ u).1 1)
    simpa only [coinducedIdentityEval, LinearMap.comp_apply, mul_one] using
      hi1.trans hf

/-- Every value of the original injected coinduced function lies in its
identity-evaluation image. -/
theorem intertwiner_value_mem_evaluationImage
    (H : Subgroup G) (ρ : Representation k H V)
    (τ : Representation k G U)
    (φ : τ.IntertwiningMap (Representation.coind H.subtype ρ))
    (u : U) (g : G) :
    (φ u).1 g ∈ (intertwinerEvaluationImage H ρ τ φ).toSubmodule := by
  refine ⟨τ g u, ?_⟩
  have hi := Representation.IntertwiningMap.isIntertwining τ
    (Representation.coind H.subtype ρ) φ g u
  have hi1 := congrArg
    (fun f : Representation.coindV H.subtype ρ => f.1 1) hi
  change (φ (τ g u)).1 1 = (φ u).1 (1 * g) at hi1
  simp only [one_mul] at hi1
  change (φ (τ g u)).1 1 = (φ u).1 g
  exact hi1

/-- Put every value of the injected layer in the canonical evaluation-image
fibre. -/
def intertwinerToEvaluationImageCoinduced
    (H : Subgroup G) (ρ : Representation k H V)
    (τ : Representation k G U)
    (φ : τ.IntertwiningMap (Representation.coind H.subtype ρ)) :
    τ.IntertwiningMap
      (Representation.coind H.subtype
        (intertwinerEvaluationImage H ρ τ φ).toRepresentation) where
  toFun u := ⟨fun g =>
    ⟨(φ u).1 g, intertwiner_value_mem_evaluationImage H ρ τ φ u g⟩, by
      intro h g
      apply Subtype.ext
      exact (φ u).2 h g⟩
  map_add' u v := by
    apply Subtype.ext
    funext g
    apply Subtype.ext
    exact congrArg (fun f : Representation.coindV H.subtype ρ => f.1 g)
      (map_add φ u v)
  map_smul' a u := by
    apply Subtype.ext
    funext g
    apply Subtype.ext
    exact congrArg (fun f : Representation.coindV H.subtype ρ => f.1 g)
      (map_smul φ a u)
  isIntertwining' g := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    funext x
    apply Subtype.ext
    have hi := Representation.IntertwiningMap.isIntertwining τ
      (Representation.coind H.subtype ρ) φ g u
    exact congrArg (fun f : Representation.coindV H.subtype ρ => f.1 x) hi

theorem intertwinerToEvaluationImageCoinduced_injective
    (H : Subgroup G) (ρ : Representation k H V)
    (τ : Representation k G U)
    (φ : τ.IntertwiningMap (Representation.coind H.subtype ρ))
    (hφ : Function.Injective φ) :
    Function.Injective (intertwinerToEvaluationImageCoinduced H ρ τ φ) := by
  intro u v huv
  apply hφ
  apply Subtype.ext
  funext g
  have hg := congrFun (congrArg Subtype.val huv) g
  exact congrArg Subtype.val hg

/-- If the quotient kernel kills the source representation, it kills the
canonical evaluation-image fibre on the stabilizer. -/
theorem evaluationImage_fibreKernel
    (π : G →* Q) (H : Subgroup G) (hK : π.ker ≤ H)
    (ρ : Representation k H V) (τ : Representation k G U)
    (hτ : π.ker ≤ τ.ker)
    (φ : τ.IntertwiningMap (Representation.coind H.subtype ρ)) :
    (subgroupImageMap π H).ker ≤
      (intertwinerEvaluationImage H ρ τ φ).toRepresentation.ker := by
  intro h hh
  apply MonoidHom.mem_ker.mpr
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  obtain ⟨u, hu⟩ := v.2
  change ρ h v.1 = v.1
  change (coinducedIdentityEval H ρ) (φ u) = v.1 at hu
  rw [← hu]
  have hi := Representation.IntertwiningMap.isIntertwining τ
    (Representation.coind H.subtype ρ) φ (h : G) u
  have hi1 := congrArg
    (fun f : Representation.coindV H.subtype ρ => f.1 1) hi
  have hhπ : (h : G) ∈ π.ker := by
    apply MonoidHom.mem_ker.mpr
    have hm := MonoidHom.mem_ker.mp hh
    exact congrArg Subtype.val hm
  have hτh : τ (h : G) = 1 := MonoidHom.mem_ker.mp (hτ hhπ)
  have hf := (φ u).2 h 1
  change (φ u).1 ((h : G) * 1) = ρ h ((φ u).1 1) at hf
  have hf' : (φ u).1 (h : G) = ρ h ((φ u).1 1) := by
    simpa only [mul_one] using hf
  have hi1' : (φ u).1 1 = (φ u).1 (h : G) := by
    change (φ (τ (h : G) u)).1 1 = (φ u).1 (1 * (h : G)) at hi1
    rw [hτh] at hi1
    simpa using hi1
  exact hf'.symm.trans hi1'.symm

/-- Canonical descent of an injected coinduced layer.  The fibre is shrunk
first to its actual evaluation image, so kernel-triviality is proved rather
than imposed on the original fibre representation. -/
def coinducedIntertwinerDescendViaEvaluationImage
    (π : G →* Q) (hπ : Function.Surjective π)
    (H : Subgroup G) (hK : π.ker ≤ H)
    (ρ : Representation k H V) (τ : Representation k G U)
    (hτ : π.ker ≤ τ.ker)
    (φ : τ.IntertwiningMap (Representation.coind H.subtype ρ)) :
    (representationDescend π hπ τ hτ).IntertwiningMap
      (Representation.coind (subgroupImage π H).subtype
        (fibreRepresentationDescend π H
          (intertwinerEvaluationImage H ρ τ φ).toRepresentation
          (evaluationImage_fibreKernel π H hK ρ τ hτ φ))) :=
  coinducedIntertwinerDescend π hπ H
    (intertwinerEvaluationImage H ρ τ φ).toRepresentation τ hτ hK
    (evaluationImage_fibreKernel π H hK ρ τ hτ φ)
    (intertwinerToEvaluationImageCoinduced H ρ τ φ)

theorem coinducedIntertwinerDescendViaEvaluationImage_injective
    (π : G →* Q) (hπ : Function.Surjective π)
    (H : Subgroup G) (hK : π.ker ≤ H)
    (ρ : Representation k H V) (τ : Representation k G U)
    (hτ : π.ker ≤ τ.ker)
    (φ : τ.IntertwiningMap (Representation.coind H.subtype ρ))
    (hφ : Function.Injective φ) :
    Function.Injective
      (coinducedIntertwinerDescendViaEvaluationImage π hπ H hK ρ τ hτ φ) :=
  coinducedIntertwinerDescend_injective π hπ H
    (intertwinerEvaluationImage H ρ τ φ).toRepresentation τ hτ hK
    (evaluationImage_fibreKernel π H hK ρ τ hτ φ)
    (intertwinerToEvaluationImageCoinduced H ρ τ φ)
    (intertwinerToEvaluationImageCoinduced_injective H ρ τ φ hφ)

end EvaluationImage

end SymmetricSubgroupAsymptotics

end
