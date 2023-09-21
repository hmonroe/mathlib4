/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/
import Mathlib.Algebra.Hom.Ring.Defs
import Mathlib.Algebra.Order.Kleene
import Mathlib.Data.List.Join
import Mathlib.Data.Set.Lattice

#align_import computability.language from "leanprover-community/mathlib"@"a239cd3e7ac2c7cde36c913808f9d40c411344f6"

/-!
# Languages

This file contains the definition and operations on formal languages over an alphabet. Note strings
are implemented as lists over the alphabet.
The operations in this file define a [Kleene algebra](https://en.wikipedia.org/wiki/Kleene_algebra)
over the languages.
-/


open List Set Computability

universe v

variable {α β γ : Type*}

/-- A language is a set of strings over an alphabet. -/
def Language (α) :=
  Set (List α)
#align language Language

instance : Membership (List α) (Language α) := ⟨Set.Mem⟩
instance : Singleton (List α) (Language α) := ⟨Set.singleton⟩
instance : Insert (List α) (Language α) := ⟨Set.insert⟩
instance : CompleteAtomicBooleanAlgebra (Language α) := Set.completeAtomicBooleanAlgebra

namespace Language

variable {l m : Language α} {a b x : List α}

-- Porting note: `reducible` attribute cannot be local.
-- attribute [local reducible] Language

/-- Zero language has no elements. -/
instance : Zero (Language α) :=
  ⟨(∅ : Set _)⟩

/-- `1 : Language α` contains only one element `[]`. -/
instance : One (Language α) :=
  ⟨{[]}⟩

instance : Inhabited (Language α) := ⟨(∅ : Set _)⟩

/-- The sum of two languages is their union. -/
instance : Add (Language α) :=
  ⟨((· ∪ ·) : Set (List α) → Set (List α) → Set (List α))⟩

/-- The product of two languages `l` and `m` is the language made of the strings `x ++ y` where
`x ∈ l` and `y ∈ m`. -/
instance : Mul (Language α) :=
  ⟨image2 (· ++ ·)⟩

lemma zero_def : (0 : Language α) = (∅ : Set _) :=
  rfl
#align language.zero_def Language.zero_def

lemma one_def : (1 : Language α) = ({[]} : Set (List α)) :=
  rfl
#align language.one_def Language.one_def

lemma add_def (l m : Language α) : l + m = (l ∪ m : Set (List α)) :=
  rfl
#align language.add_def Language.add_def

lemma mul_def (l m : Language α) : l * m = image2 (· ++ ·) l m :=
  rfl
#align language.mul_def Language.mul_def

/-- The Kleene star of a language `L` is the set of all strings which can be written by
concatenating strings from `L`. -/
instance : KStar (Language α) := ⟨fun l ↦ {x | ∃ L : List (List α), x = L.join ∧ ∀ y ∈ L, y ∈ l}⟩

lemma kstar_def (l : Language α) : l∗ = {x | ∃ L : List (List α), x = L.join ∧ ∀ y ∈ L, y ∈ l} :=
  rfl
#align language.kstar_def Language.kstar_def

-- Porting note: `reducible` attribute cannot be local,
--               so this new theorem is required in place of `Set.ext`.
@[ext]
lemma ext {l m : Language α} (h : ∀ (x : List α), x ∈ l ↔ x ∈ m) : l = m :=
  Set.ext h

@[simp]
lemma not_mem_zero (x : List α) : x ∉ (0 : Language α) :=
  id
#align language.not_mem_zero Language.not_mem_zero

@[simp]
lemma mem_one (x : List α) : x ∈ (1 : Language α) ↔ x = [] := by rfl
#align language.mem_one Language.mem_one

lemma nil_mem_one : [] ∈ (1 : Language α) :=
  Set.mem_singleton _
#align language.nil_mem_one Language.nil_mem_one

lemma mem_add (l m : Language α) (x : List α) : x ∈ l + m ↔ x ∈ l ∨ x ∈ m :=
  Iff.rfl
#align language.mem_add Language.mem_add

lemma mem_mul : x ∈ l * m ↔ ∃ a b, a ∈ l ∧ b ∈ m ∧ a ++ b = x :=
  mem_image2
#align language.mem_mul Language.mem_mul

lemma append_mem_mul : a ∈ l → b ∈ m → a ++ b ∈ l * m :=
  mem_image2_of_mem
#align language.append_mem_mul Language.append_mem_mul

lemma mem_kstar : x ∈ l∗ ↔ ∃ L : List (List α), x = L.join ∧ ∀ y ∈ L, y ∈ l :=
  Iff.rfl
#align language.mem_kstar Language.mem_kstar

lemma join_mem_kstar {L : List (List α)} (h : ∀ y ∈ L, y ∈ l) : L.join ∈ l∗ :=
  ⟨L, rfl, h⟩
#align language.join_mem_kstar Language.join_mem_kstar

lemma nil_mem_kstar (l : Language α) : [] ∈ l∗ :=
  ⟨[], rfl, fun _ h ↦ by contradiction⟩
#align language.nil_mem_kstar Language.nil_mem_kstar

instance instSemiring : Semiring (Language α) where
  add := (· + ·)
  add_assoc := union_assoc
  zero := 0
  zero_add := empty_union
  add_zero := union_empty
  add_comm := union_comm
  mul := (· * ·)
  mul_assoc _ _ _ := image2_assoc append_assoc
  zero_mul _ := image2_empty_left
  mul_zero _ := image2_empty_right
  one := 1
  one_mul l := by simp [mul_def, one_def]
  mul_one l := by simp [mul_def, one_def]
  natCast n := if n = 0 then 0 else 1
  natCast_zero := rfl
  natCast_succ n := by cases n <;> simp [Nat.cast, add_def, zero_def]
  left_distrib _ _ _ := image2_union_right
  right_distrib _ _ _ := image2_union_left

@[simp]
lemma add_self (l : Language α) : l + l = l :=
  sup_idem
#align language.add_self Language.add_self

/-- Maps the alphabet of a language. -/
def map (f : α → β) : Language α →+* Language β where
  toFun := image (List.map f)
  map_zero' := image_empty _
  map_one' := image_singleton
  map_add' := image_union _
  map_mul' _ _ := image_image2_distrib <| map_append _
#align language.map Language.map

@[simp]
lemma map_id (l : Language α) : map id l = l := by simp [map]
#align language.map_id Language.map_id

@[simp]
lemma map_map (g : β → γ) (f : α → β) (l : Language α) : map g (map f l) = map (g ∘ f) l := by
  simp [map, image_image]
#align language.map_map Language.map_map

lemma kstar_def_nonempty (l : Language α) :
    l∗ = { x | ∃ S : List (List α), x = S.join ∧ ∀ y ∈ S, y ∈ l ∧ y ≠ [] } := by
  ext x
  constructor
  · rintro ⟨S, rfl, h⟩
    refine' ⟨S.filter fun l ↦ ¬List.isEmpty l, by simp, fun y hy ↦ _⟩
    -- Porting note: The previous code was:
    -- rw [mem_filter, empty_iff_eq_nil] at hy
    rw [mem_filter, decide_not, Bool.decide_coe, Bool.not_eq_true', ← Bool.bool_iff_false,
      isEmpty_iff_eq_nil] at hy
    exact ⟨h y hy.1, hy.2⟩
  · rintro ⟨S, hx, h⟩
    exact ⟨S, hx, fun y hy ↦ (h y hy).1⟩
#align language.kstar_def_nonempty Language.kstar_def_nonempty

lemma le_iff (l m : Language α) : l ≤ m ↔ l + m = m :=
  sup_eq_right.symm
#align language.le_iff Language.le_iff

lemma le_mul_congr {l₁ l₂ m₁ m₂ : Language α} : l₁ ≤ m₁ → l₂ ≤ m₂ → l₁ * l₂ ≤ m₁ * m₂ := by
  intro h₁ h₂ x hx
  simp only [mul_def, exists_and_left, mem_image2, image_prod] at hx ⊢
  tauto
#align language.le_mul_congr Language.le_mul_congr

lemma le_add_congr {l₁ l₂ m₁ m₂ : Language α} : l₁ ≤ m₁ → l₂ ≤ m₂ → l₁ + l₂ ≤ m₁ + m₂ :=
  sup_le_sup
#align language.le_add_congr Language.le_add_congr

lemma mem_iSup {ι : Sort v} {l : ι → Language α} {x : List α} : (x ∈ ⨆ i, l i) ↔ ∃ i, x ∈ l i :=
  mem_iUnion
#align language.mem_supr Language.mem_iSup

lemma iSup_mul {ι : Sort v} (l : ι → Language α) (m : Language α) :
    (⨆ i, l i) * m = ⨆ i, l i * m :=
  image2_iUnion_left _ _ _
#align language.supr_mul Language.iSup_mul

lemma mul_iSup {ι : Sort v} (l : ι → Language α) (m : Language α) :
    (m * ⨆ i, l i) = ⨆ i, m * l i :=
  image2_iUnion_right _ _ _
#align language.mul_supr Language.mul_iSup

lemma iSup_add {ι : Sort v} [Nonempty ι] (l : ι → Language α) (m : Language α) :
    (⨆ i, l i) + m = ⨆ i, l i + m :=
  iSup_sup
#align language.supr_add Language.iSup_add

lemma add_iSup {ι : Sort v} [Nonempty ι] (l : ι → Language α) (m : Language α) :
    (m + ⨆ i, l i) = ⨆ i, m + l i :=
  sup_iSup
#align language.add_supr Language.add_iSup

lemma mem_pow {l : Language α} {x : List α} {n : ℕ} :
    x ∈ l ^ n ↔ ∃ S : List (List α), x = S.join ∧ S.length = n ∧ ∀ y ∈ S, y ∈ l := by
  induction' n with n ihn generalizing x
  · simp only [mem_one, pow_zero, length_eq_zero]
    constructor
    · rintro rfl
      exact ⟨[], rfl, rfl, fun _ h ↦ by contradiction⟩
    · rintro ⟨_, rfl, rfl, _⟩
      rfl
  · simp only [pow_succ, mem_mul, ihn]
    constructor
    · rintro ⟨a, b, ha, ⟨S, rfl, rfl, hS⟩, rfl⟩
      exact ⟨a :: S, rfl, rfl, forall_mem_cons.2 ⟨ha, hS⟩⟩
    · rintro ⟨_ | ⟨a, S⟩, rfl, hn, hS⟩ <;> cases hn
      rw [forall_mem_cons] at hS
      exact ⟨a, _, hS.1, ⟨S, rfl, rfl, hS.2⟩, rfl⟩
#align language.mem_pow Language.mem_pow

lemma kstar_eq_iSup_pow (l : Language α) : l∗ = ⨆ i : ℕ, l ^ i := by
  ext x
  simp only [mem_kstar, mem_iSup, mem_pow]
  constructor
  · rintro ⟨S, rfl, hS⟩
    exact ⟨_, S, rfl, rfl, hS⟩
  · rintro ⟨_, S, rfl, rfl, hS⟩
    exact ⟨S, rfl, hS⟩
#align language.kstar_eq_supr_pow Language.kstar_eq_iSup_pow

@[simp]
lemma map_kstar (f : α → β) (l : Language α) : map f l∗ = (map f l)∗ := by
  rw [kstar_eq_iSup_pow, kstar_eq_iSup_pow]
  simp_rw [← map_pow]
  exact image_iUnion
#align language.map_kstar Language.map_kstar

lemma mul_self_kstar_comm (l : Language α) : l∗ * l = l * l∗ := by
  simp only [kstar_eq_iSup_pow, mul_iSup, iSup_mul, ← pow_succ, ← pow_succ']
#align language.mul_self_kstar_comm Language.mul_self_kstar_comm

@[simp]
lemma one_add_self_mul_kstar_eq_kstar (l : Language α) : 1 + l * l∗ = l∗ := by
  simp only [kstar_eq_iSup_pow, mul_iSup, ← pow_succ, ← pow_zero l]
  exact sup_iSup_nat_succ _
#align language.one_add_self_mul_kstar_eq_kstar Language.one_add_self_mul_kstar_eq_kstar

@[simp]
lemma one_add_kstar_mul_self_eq_kstar (l : Language α) : 1 + l∗ * l = l∗ := by
  rw [mul_self_kstar_comm, one_add_self_mul_kstar_eq_kstar]
#align language.one_add_kstar_mul_self_eq_kstar Language.one_add_kstar_mul_self_eq_kstar

instance : KleeneAlgebra (Language α) :=
  { Language.instSemiring, Set.completeAtomicBooleanAlgebra with
    kstar := fun L ↦ L∗,
    one_le_kstar := fun a l hl ↦ ⟨[], hl, by simp⟩,
    mul_kstar_le_kstar := fun a ↦ (one_add_self_mul_kstar_eq_kstar a).le.trans' le_sup_right,
    kstar_mul_le_kstar := fun a ↦ (one_add_kstar_mul_self_eq_kstar a).le.trans' le_sup_right,
    kstar_mul_le_self := fun l m h ↦ by
      rw [kstar_eq_iSup_pow, iSup_mul]
      refine' iSup_le (fun n ↦ _)
      induction' n with n ih
      · simp
      rw [pow_succ', mul_assoc (l^n) l m]
      exact le_trans (le_mul_congr le_rfl h) ih,
    mul_kstar_le_self := fun l m h ↦ by
      rw [kstar_eq_iSup_pow, mul_iSup]
      refine' iSup_le (fun n ↦ _)
      induction' n with n ih
      · simp
      rw [pow_succ, ←mul_assoc m l (l^n)]
      exact le_trans (le_mul_congr h le_rfl) ih }

end Language
