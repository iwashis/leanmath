import Mathlib
import Mathlib.Order.Lattice
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Order.AbsoluteValue
import Mathlib.Data.Real.Basic
import Mathlib.Init.Algebra.Classes


-- Basic definitions:
class normed_vectorspace (V : Type*)
  [AddCommGroup V]
  [Module ℝ V] :=
( norm: V → ℝ )
(norm_pos : ∀ x, norm x ≥  0)
(norm_eq_zero : ∀ x, norm x = 0 ↔ x = 0)
(norm_add : ∀ x y, norm (x + y) ≤ norm x + norm y)
(norm_smul : ∀ (c : ℝ) (x : V), norm (c • x) = |c| * norm x)

def is_cauchy {V : Type*}
  [AddCommGroup V]
  [Module ℝ V]
  [nvs: normed_vectorspace V]
  (s : ℕ → V) : Prop :=
∀ ε > 0, ∃ N, ∀ m n : ℕ , (m ≥ N) → nvs.norm ( s ( m + n ) - s m) < ε


def convergent_to {V : Type*}
  [AddCommGroup V]
  [Module ℝ V]
  [nvs: normed_vectorspace V]
  (s : ℕ → V ) (x : V): Prop := ∀ ε > 0, ∃ N, ∀ m ≥ N, nvs.norm ( s m + (- x)) < ε

def is_convergent {V : Type*}
  [AddCommGroup V]
  [Module ℝ V]
  [normed_vectorspace V]
  (s : ℕ → V ) : Prop :=
 ∃ x : V, convergent_to s x


class banach_space (V : Type*)
  [AddCommGroup V]
  [Module ℝ V]
  [normed_vectorspace V] :=
(f_cauchy_then_conv: ∀  (s : ℕ → V) , is_cauchy (s) → is_convergent (s))


def is_contractive_mapping {V : Type*}
  [AddCommGroup V]
  [Module ℝ V]
  [nvs : normed_vectorspace V]
  (f :V → V) : Prop :=
    ∃ K, K > 0 ∧ K < 1 ∧  ∀ x y ,
    nvs.norm ( f x + (- f y) ) ≤ K * nvs.norm ( x + (- y) )


-- Basic lemmas:
lemma norm_negation {V : Type*}
  [AddCommGroup V]
  [Module ℝ V]
  [nvs: normed_vectorspace V]
  (x : V) : nvs.norm x = nvs.norm (-x) := by
  rw [← neg_one_smul ℝ x]
  rw [nvs.norm_smul (-1) x]
  rw [abs_neg]
  rw [abs_one]
  rw [one_mul]


lemma neg_equal  (x y : ℝ ) : ¬ (x = y) → ¬ (y = x) := by
  intro h
  intro h'
  apply h
  rw [h']

lemma zero_real (x : ℝ) (h1: x ≥ 0) (h2 : ∀ ε > 0, x < ε) : x = 0 := by
  by_contra h
  have hx : x > 0 := lt_of_le_of_ne h1 (neg_equal x 0 h)
  let hx2 := h2 x hx
  linarith [hx, hx2]


lemma uniqueness_of_limits {V : Type*}
  [AddCommGroup V]
  [Module ℝ V]
  [nvs: normed_vectorspace V]
  (s : ℕ → V ) (x y : V) : convergent_to s x ∧ convergent_to s y → x = y := by
  intro ⟨ conv_x , conv_y ⟩
  let h : nvs.norm (x + (- y)) = 0 := by
    let h' : ∀ ε > 0, nvs.norm ( x + ( -y )) < ε := by
      intro ε hε
      let hε' : ε / 2 > 0 := by linarith
      let ⟨ Nx , hNx ⟩ := conv_x ( ε / 2 ) hε'
      let ⟨ Ny , hNy ⟩ := conv_y ( ε / 2) hε'
      let N := max Nx Ny
      let NgeqNx : N ≥ Nx := by
        apply le_max_left
      let NgeqNy : N ≥ Ny := by
        apply le_max_right
      let norm_sN_x' := hNx N NgeqNx
      let norm_sN_x : normed_vectorspace.norm (x + (-s N)) < ε / 2  := by
        rw [norm_negation]
        rw[neg_add]
        rw[neg_neg]
        rw[add_comm]
        apply norm_sN_x'

      let norm_sN_y := hNy N NgeqNy

      let eq : x + (-y) = (x + (- s N)) +  (s N + (- y)) := by
        rw [add_assoc x (-s N) (s N + (-y))]
        rw [← add_assoc (-s N) (s N) (-y)]
        rw [add_comm (-s N) (s N)]
        rw [add_neg_self]
        rw [add_comm 0 (-y)]
        rw [add_zero]

      let  key_inequality : nvs.norm ( x + (-y)) ≤ nvs.norm ( x  + ( - s N)) + nvs.norm ( s N + (- y)) := by
        rw [eq]
        apply nvs.norm_add

      have final : nvs.norm ( x + (-y)) < ε := by
        linarith [ norm_sN_x , norm_sN_y ,key_inequality ]
      exact final
    exact zero_real (nvs.norm ( x + -y)) (nvs.norm_pos ( x + -y ))  h'
  let h' := (nvs.norm_eq_zero (x + (- y))).mp h
  rw [add_neg_eq_zero] at h'
  exact h'


open Nat

def f_sequence { V : Type* }: V → (V → V) → ℕ → V :=
  fun x f n => match n with
    | zero =>  x
    | succ n => f (f_sequence x f n)


-- Tiny helpers:
lemma eq_f_zero {V : Type*}
  [AddCommGroup V]
  [Module ℝ V]
  (f : V → V): f_sequence 0 f 0 = 0 := rfl

lemma eq_f_n  {V: Type*}
  [AddCommGroup V]
  [Module ℝ V]
  (f : V → V): ∀ n, f_sequence 0 f (succ n) = f (f_sequence 0 f n) := by
      intro n
      rfl

lemma succ_inequality {m N} : m ≥ succ N → ∃ m', m = succ m' := by
  intro h
  induction m with
    | zero => linarith
    | succ m _ => exact ⟨ m , rfl ⟩


-- Bigger helpers:
lemma contractive_implies_cauchy {V : Type*}
  [AddCommGroup V]
  [Module ℝ V]
  [ns : normed_vectorspace V]
  [bs : banach_space V]
  ( f : V → V ) ( iscontr : is_contractive_mapping ( f ) ) : is_cauchy ( f_sequence 0 f )
  := by
  let ⟨k , k_gt_0 , k_lt_1 , h ⟩ := iscontr
  intro ε hε
  sorry -- sorry :(

theorem fix_point_existence {V : Type*}
  [AddCommGroup V]
  [Module ℝ V]
  [ns : normed_vectorspace V]
  -- the hypothesis:
  [bs : banach_space V ]
  -- the statement:
  : ∀ ( f : V → V ), is_contractive_mapping ( f ) → ∃ x, f x = x
  := by
  intro f iscontr
  let ⟨ K , K_gt_0 , _ , contractive_condition ⟩ := iscontr
  let s := f_sequence 0 f
  let eq_s : ∀ n, s n = f_sequence 0 f n := by
    intro n
    rfl
  let iscauchy_s := contractive_implies_cauchy f iscontr
  let isconv_s := bs.f_cauchy_then_conv s iscauchy_s
  let ⟨ x , h ⟩ := isconv_s
  let h' : convergent_to s (f x) := by
    intro ε' hε'
    let hε'_over_K : (ε' / K) > 0 := by
      exact div_pos hε' K_gt_0
    let ⟨ N , hN ⟩  := h (ε'/ K) hε'_over_K
    have hN' : ∀ m ≥ succ N, ns.norm ( s m + (- f x)) < ε' := by
      intro m hm
      let ⟨ m' , hm' ⟩ := succ_inequality hm -- m' is such that m = succ m'
      let m'_geq_N : m' ≥ N := by
        linarith
      let hN_m' : ns.norm ( f_sequence 0 f m' + -x) < ε' / K := by
        rw [← eq_s]
        exact hN m' m'_geq_N
      let KhN_m' : K * ns.norm ( f_sequence 0 f m' + -x) < K* (ε' / K) := by
        exact mul_lt_mul_of_pos_left hN_m' K_gt_0
      calc ns.norm (s m + -f x) = ns.norm (f_sequence 0 f m + -f x) := by rw [eq_s]
      ns.norm (f_sequence 0 f m + -f x) = ns.norm (f_sequence 0 f (succ m') + -f x) := by rw [hm']
      ns.norm (f_sequence 0 f (succ m') + -f x) = ns.norm (( f (f_sequence 0 f m') ) + -f x) := by rw [eq_f_n f m']
      ns.norm (( f (f_sequence 0 f m') ) + -f x) ≤ K * ns.norm ( f_sequence 0 f m' + -x) := by exact contractive_condition (f_sequence 0 f m') x
      K * ns.norm ( f_sequence 0 f m' + -x) < K * ( ε' / K )  := by exact KhN_m'
      K * (ε' / K)  = ε' := by field_simp; ring
    exact ⟨ succ N , hN' ⟩
  exact ⟨ x , uniqueness_of_limits s (f x) x  ⟨ h' , h ⟩ ⟩
