{-# OPTIONS --warning=noUnsupportedIndexedMatch #-}
open import Agda.Primitive using (Level; lzero)

module TestStdlib where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans)

-- 證明：對任意 n，都有 n ≤ suc n
n≤suc : ∀ (n : ℕ) → n ≤ suc n
n≤suc zero    = z≤n
n≤suc (suc n) = s≤s (n≤suc n)

-- 定義一個簡單函式，表示加一
inc : ℕ → ℕ
inc n = suc n

-- 定義引理 test：如果 x ≤ y，則 x ≤ suc y
test : ∀ (x y : ℕ) → x ≤ y → x ≤ suc y
test x y p = ≤-trans p (n≤suc y)




