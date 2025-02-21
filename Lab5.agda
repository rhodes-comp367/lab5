module Lab5 where

data Nat : Set where
  zero : Nat
  suc : Nat → Nat
{-# BUILTIN NATURAL Nat #-}

data Nat= : Nat → Nat → Set where
  zero= : Nat= zero zero
  suc= : {m n : Nat} → Nat= m n → Nat= (suc m) (suc n)

data Even : Nat → Set where
  zero : Even zero
  suc-suc : {n : Nat} → Even n → Even (suc (suc n))

data Odd : Nat → Set where
  one : Odd (suc zero)
  suc-suc : {n : Nat} → Odd n → Odd (suc (suc n))

refl : (n : Nat) → Nat= n n
refl zero = zero=
refl (suc n) = suc= (refl n)

sym : {m n : Nat} → Nat= m n → Nat= n m
sym zero= = zero=
sym (suc= e) = suc= (sym e)

trans : {l m n : Nat} → Nat= l m → Nat= m n → Nat= l n
trans zero= zero= = zero=
trans (suc= e) (suc= f) = suc= (trans e f)

_+_ : Nat → Nat → Nat
zero + n = n
suc m + n = suc (m + n)
infix 6 _+_

_*_ : Nat → Nat → Nat
zero * _ = zero
suc m * n = n + m * n
infix 7 _*_

-- convert 0 to 1 and nonzero numbers to 0.
flip : Nat → Nat
flip zero = 1
flip (suc _) = 0

-- the sequence 1, 3, 5, ..., defined recursively.
a : Nat → Nat
a zero = 1
a (suc n) = 2 + a n

-- the sequence 1, 3, 5, ..., defined directly.
b : Nat → Nat
b n = 1 + n * 2

-- the sequence 1, 0, 1, 0, ...
c : Nat → Nat
c zero = 1
c (suc n) = flip (c n)

-- the terms of a & b are equal.
equal : (n : Nat) → Nat= (a n) (b n)
equal = ?

-- `sum n a` is the sum of the first n terms of a.
-- (for example, `sum 2 a` should be `a 0 + a 1`.)
sum : Nat → (Nat → Nat) → Nat
sum = ?

-- 0 + 0 + ... + 0 = 0.
0-sum : (n : Nat) → Nat= (sum n (λ _ → 0)) 0
0-sum = ?

-- 1 + 1 + ... + 1 = n, where n is the number of terms.
1-sum : (n : Nat) → Nat= (sum n (λ _ → 1)) n
1-sum = ?

-- the even-indexed terms of c are 1.
c-even : {n : Nat} → Even n → Nat= (c n) 1
c-even = ?

-- the odd-indexed terms of c are 0.
c-odd : {n : Nat} → Odd n → Nat= (c n) 0
c-odd = ?

-- mulitplying by two is the same as adding to itself.
times2 : (n : Nat) → Nat= (n * 2) (n + n)
times2 = ?

-- plus respects equality of second argument.
plus= : (a : Nat) → {b c : Nat} → Nat= b c → Nat= (a + b) (a + c)
plus= = ?

-- an identity of natural numbers. (** do this last **)
identity : (n : Nat) → Nat= ((1 + n) * (1 + n)) ((1 + n * 2) + n * n)
identity = ?

-- the sum of the first n terms of b is n^2.
b-sum : (n : Nat) → Nat= (sum n b) (n * n)
b-sum = ?

