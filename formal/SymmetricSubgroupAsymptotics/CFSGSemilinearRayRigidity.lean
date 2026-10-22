import Mathlib.LinearAlgebra.Pi

/-! The field component of a semilinear map fixing all actual rays is
trivial as soon as two coordinate directions exist. Only the literal
vectors e_i+e_j and e_i+t e_j are used; no projective recognition input. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSemilinearRayRigidity
variable {K I : Type*} [Field K] [DecidableEq I]

theorem field_eq_id (σ : K→+*K) (f : (I→K)→ₛₗ[σ](I→K))
    (i j : I) (hij : i≠j)
    (hfix : ∀w : I→K,w≠0 → ∃c : K,c≠0 ∧ f w=c•w) : σ=RingHom.id K := by
  let u : I→K := Pi.single i 1
  let v : I→K := Pi.single j 1
  have hu : u≠0 := by
    intro h
    have hh := congrFun h i
    simpa [u] using hh
  have hv : v≠0 := by
    intro h
    have hh := congrFun h j
    simpa [v] using hh
  have huv : u+v≠0 := by
    intro h
    have hh := congrFun h i
    simpa [u,v,Pi.single_apply,hij] using hh
  obtain ⟨a,ha0,ha⟩ := hfix u hu
  obtain ⟨b,_,hb⟩ := hfix v hv
  obtain ⟨c,_,hc⟩ := hfix (u+v) huv
  have hadd := f.map_add u v
  rw [hc,ha,hb] at hadd
  have hca : c=a := by
    simpa [u,v,Pi.single_apply,hij] using congrFun hadd i
  have hcb : c=b := by
    simpa [u,v,Pi.single_apply,Ne.symm hij] using congrFun hadd j
  apply RingHom.ext
  intro t
  have hut : u+t•v≠0 := by
    intro h
    have hh := congrFun h i
    simpa [u,v,Pi.single_apply,hij] using hh
  obtain ⟨d,_,hd⟩ := hfix (u+t•v) hut
  have hmap := f.map_add u (t•v)
  rw [hd,f.map_smulₛₗ,ha,hb] at hmap
  have hda : d=a := by
    simpa [u,v,Pi.single_apply,hij] using congrFun hmap i
  have hj : d*t=σ t*b := by
    simpa [u,v,Pi.single_apply,Ne.symm hij,smul_smul] using congrFun hmap j
  have hmul : a*t=a*σ t := by
    rw [hda,←hcb,hca] at hj
    exact hj.trans (mul_comm _ _)
  exact (mul_left_cancel₀ ha0 hmul).symm

end SymmetricSubgroupAsymptotics.CFSGSemilinearRayRigidity
