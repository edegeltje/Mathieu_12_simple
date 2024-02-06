import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.GroupTheory.SpecificGroups.Alternating

import Mathieu12Simple.F4

open F4
open Subspace
open Submodule

abbrev F₄6 : Type := Fin 6 → F₄


namespace F46
open F4
section base_instances

end base_instances
section definition_theorems


@[simp]
theorem add_def (a b : F₄6) (n:Fin 6): (a + b) n = a n + b n := by
  rfl

@[simp]
theorem zero_def (n:Fin 6): (0:F₄6) n = 0 := by
  rfl

@[simp]
theorem smul_def (x : F₄) (a : F₄6) (n : Fin 6): (x • a) n = x * a n := by
  rfl

@[simp]
theorem neg_def (a:F₄6) (n : Fin 6): (-a) n = -(a n) := by
  rfl

end definition_theorems

instance : AddCommMonoid F₄6 where
  add_assoc := by
    intro a b c
    ext : 1
    simp only [add_def]
    rw [add_assoc]
  zero_add := by
    intro a
    ext : 1
    simp
  add_zero := by
    intro a
    ext : 1
    rw [add_def,zero_def]
    ring_nf
  add_comm := by
    intro a b
    ext : 1
    rw [add_def,add_def]
    ring_nf

instance : AddCommGroup F₄6 where
  add_left_neg := by
    intro a
    ext : 1
    simp
  add_comm := add_comm

instance : Module F₄ F₄6 where
  one_smul := by
    intro b
    ext : 1
    rw [smul_def]
    ring_nf
  mul_smul := by
    intro x y b
    ext : 1
    rw [smul_def, smul_def,smul_def]
    ring_nf
  smul_zero := by
    intro a
    ext : 1
    rw [smul_def, zero_def]
    ring_nf
  smul_add := by
    intro a x y
    ext : 1
    rw [smul_def,add_def]
    rw [add_def,smul_def,smul_def]
    ring_nf
  add_smul := by
    intro r s x
    ext : 1
    rw [smul_def,add_def]
    rw [smul_def,smul_def]
    ring_nf
  zero_smul := by
    intro x
    ext : 1
    rw [smul_def]
    rw [zero_def]
    ring_nf
end F46

namespace HexaCode

def b₁ : F₄6 := ![ω,ω⁻¹,ω⁻¹,ω,ω⁻¹,ω]
def b₂ : F₄6 := ![ω⁻¹,ω,ω,ω⁻¹,ω⁻¹,ω]
def b₃ : F₄6 := ![ω⁻¹,ω,ω⁻¹,ω,ω,ω⁻¹]


abbrev HC_Basis : Set F₄6 := {b₁,b₂,b₃}

end HexaCode

instance HexaCode : Subspace F₄ F₄6 := Submodule.span F₄ HexaCode.HC_Basis

namespace HexaCode
def a₁ : F₄6 := ![ω,ω⁻¹,ω,ω⁻¹,ω,ω⁻¹]

lemma a_one_mem_hexacode: a₁ ∈ HexaCode := by
  rw [HexaCode]
  apply mem_span_set'.mpr
  use 3
  use ![1,1,1]
  use ![⟨b₁,Or.inl rfl⟩,⟨b₂,Or.inr (Or.inl rfl)⟩,⟨b₃,Or.inr (Or.inr rfl)⟩]
  exact List.ofFn_inj.mp rfl

-- automorphisms are change of basis, linear map.
abbrev HexaCode_Automorphisms : Type := AddAut HexaCode -- group of automorphisms of the hexacode

theorem hexacode_automorphisms_is_3A5 : sorry := sorry

-- HexaCode modulo scalar multiplication is just linear sums of b₂ and b₃, with b₁ added.
abbrev HexaCode_mod_scalar : Type := sorry

end HexaCode
