/-
  How the token's `ft_resolve_transfer` return value reaches `ft_resolve_withdraw`.

  near-sdk serializes a `U128` return value as a JSON string of decimal digits (`"123"`);
  the receiving side reads it back with `serde_json::from_slice::<U128>` (the reader is
  `ProvedFT.parseU128Json`, the same one the token model uses for `ft_on_transfer` results).
  `parse_enc` proves that the reader returns the number that was written, so the encoding is not
  an assumption of the theorems.
-/
import ProvedFT.Model
import Intents.Basic

namespace Intents
open ProvedFT

/-- Decimal digits (ASCII codes), most significant first; fuel `k` allows `k + 1` digits. -/
def decAux : Nat → Nat → List Nat
  | 0, n => [0x30 + n % 10]
  | k + 1, n => if n < 10 then [0x30 + n] else decAux k (n / 10) ++ [0x30 + n % 10]

/-- `serde_json::to_vec(&U128(n))`: the decimal digits of `n` between two double quotes. -/
def encU128 (n : Nat) : List Nat := 0x22 :: (decAux 39 n ++ [0x22])

def IsDig (c : Nat) : Prop := 0x30 ≤ c ∧ c ≤ 0x39

theorem decAux_dig (k n : Nat) : ∀ c ∈ decAux k n, IsDig c := by
  induction k generalizing n with
  | zero =>
    intro c hc
    simp only [decAux, List.mem_singleton] at hc
    subst hc; unfold IsDig; omega
  | succ k ih =>
    intro c hc
    simp only [decAux] at hc
    by_cases hn : n < 10
    · rw [ifP hn] at hc
      simp only [List.mem_singleton] at hc
      subst hc; unfold IsDig; omega
    · rw [ifN hn] at hc
      rcases List.mem_append.mp hc with h | h
      · exact ih _ c h
      · simp only [List.mem_singleton] at h
        subst h; unfold IsDig; omega

theorem decAux_ne_nil (k n : Nat) : decAux k n ≠ [] := by
  cases k with
  | zero => simp [decAux]
  | succ k =>
    simp only [decAux]
    by_cases hn : n < 10
    · rw [ifP hn]; simp
    · rw [ifN hn]; simp

theorem decAux_length (k n : Nat) : (decAux k n).length ≤ k + 1 := by
  induction k generalizing n with
  | zero => simp [decAux]
  | succ k ih =>
    simp only [decAux]
    by_cases hn : n < 10
    · rw [ifP hn]; simp
    · rw [ifN hn]
      have := ih (n / 10)
      simp only [List.length_append, List.length_singleton]; omega

theorem digitsVal_snoc (ds : List Nat) (d : Nat) :
    digitsVal (ds ++ [0x30 + d]) = digitsVal ds * 10 + d := by
  simp only [digitsVal, List.foldl_append, List.foldl_cons, List.foldl_nil]
  omega

theorem digitsVal_decAux (k n : Nat) (h : n < 10 ^ (k + 1)) : digitsVal (decAux k n) = n := by
  induction k generalizing n with
  | zero =>
    have h' : n < 10 := by simpa using h
    simp only [decAux, digitsVal, List.foldl_cons, List.foldl_nil]
    omega
  | succ k ih =>
    simp only [decAux]
    by_cases hn : n < 10
    · rw [ifP hn]
      simp only [digitsVal, List.foldl_cons, List.foldl_nil]
      omega
    · rw [ifN hn, digitsVal_snoc]
      have hd : n / 10 < 10 ^ (k + 1) := by
        apply Nat.div_lt_of_lt_mul
        rw [Nat.pow_succ, Nat.mul_comm] at h
        exact h
      rw [ih _ hd]; omega

theorem strBody_digits (ds : List Nat) (h : ∀ c ∈ ds, IsDig c) (tail : List Nat) :
    strBody (ds ++ 0x22 :: tail) = some (ds, tail) := by
  induction ds with
  | nil => simp [strBody]
  | cons d t ih =>
    have hd := h d (by simp)
    have ht := ih (fun c hc => h c (by simp [hc]))
    unfold IsDig at hd
    have hcase : d = 48 ∨ d = 49 ∨ d = 50 ∨ d = 51 ∨ d = 52 ∨ d = 53 ∨ d = 54 ∨ d = 55 ∨
        d = 56 ∨ d = 57 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [strBody, ht]

theorem all_digits (ds : List Nat) (h : ∀ c ∈ ds, IsDig c) : ds.all isDigitB = true := by
  rw [List.all_eq_true]
  intro c hc
  have := h c hc
  unfold IsDig at this
  simp [isDigitB, this.1, this.2]

theorem parseU128Str_digits (ds : List Nat) (hne : ds ≠ []) (h : ∀ c ∈ ds, IsDig c)
    (hv : digitsVal ds ≤ U128_MAX) : parseU128Str ds = some (digitsVal ds) := by
  cases ds with
  | nil => exact absurd rfl hne
  | cons d t =>
    have hd := h d (by simp)
    unfold IsDig at hd
    have ht := all_digits t (fun c hc => h c (by simp [hc]))
    have hcase : d = 48 ∨ d = 49 ∨ d = 50 ∨ d = 51 ∨ d = 52 ∨ d = 53 ∨ d = 54 ∨ d = 55 ∨
        d = 56 ∨ d = 57 := by omega
    unfold parseU128Str
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [ht, hv, isDigitB]

/-- The reader returns what the writer wrote. -/
theorem parse_enc (n : Nat) (h : n ≤ U128_MAX) : parseU128Json (encU128 n) = some n := by
  have hlt : n < 10 ^ (39 + 1) := by
    have : U128_MAX < 10 ^ (39 + 1) := by decide
    omega
  have hv := digitsVal_decAux 39 n hlt
  have hs := strBody_digits (decAux 39 n) (decAux_dig 39 n) []
  have hp := parseU128Str_digits (decAux 39 n) (decAux_ne_nil 39 n) (decAux_dig 39 n)
    (by rw [hv]; exact h)
  unfold parseU128Json encU128
  have hw : isWs 0x22 = false := by decide
  simp only [List.dropWhile_cons, hw]
  simp [hs, hp, hv]

theorem enc_length (n : Nat) : (encU128 n).length ≤ 42 := by
  have := decAux_length 39 n
  simp only [encU128, List.length_cons, List.length_append, List.length_nil]
  omega

end Intents
