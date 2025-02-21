module Lab5Sol where

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

-- helper function for c-odd.
flip-flip0 : {n : Nat} → Nat= n 0 → Nat= (flip (flip n)) 0
flip-flip0 zero= = zero=

-- helper function for c-even.
flip-flip1 : {n : Nat} → Nat= n 1 → Nat= (flip (flip n)) 1
flip-flip1 (suc= zero=) = suc= zero=

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
equal zero = suc= zero=
equal (suc n) = suc= (suc= (equal n))

-- sum the first n terms of a sequence.
sum : Nat → (Nat → Nat) → Nat
sum zero _ = zero
sum (suc n) f = f n + sum n f

-- 0 + 0 + ... + 0 = 0.
0-sum : (n : Nat) → Nat= (sum n (λ _ → 0)) 0
0-sum zero = zero=
0-sum (suc n) = 0-sum n

-- 1 + 1 + ... + 1 = n, where n is the number of terms.
1-sum : (n : Nat) → Nat= (sum n (λ _ → 1)) n
1-sum zero = zero=
1-sum (suc n) = suc= (1-sum n)

-- the even-indexed terms of c are 1.
c-even : {n : Nat} → Even n → Nat= (c n) 1
c-even zero = suc= zero=
c-even (suc-suc e) = flip-flip1 (c-even e)

-- the odd-indexed terms of c are 0.
c-odd : {n : Nat} → Odd n → Nat= (c n) 0
c-odd one = zero=
c-odd (suc-suc o) = flip-flip0 (c-odd o)

-- helper function for times2.
plus-suc : (m n : Nat) → Nat= (m + suc n) (suc (m + n))
plus-suc zero n = refl (suc n)
plus-suc (suc m) n = suc= (plus-suc m n)

-- mulitplying by two is the same as adding to itself.
times2 : (n : Nat) → Nat= (n * 2) (n + n)
times2 zero = zero=
times2 (suc n) = suc=
  (trans (suc= (times2 n))
  (sym (plus-suc n n)))

plus= : (a : Nat) → {b c : Nat} → Nat= b c → Nat= (a + b) (a + c)
plus= zero e = e
plus= (suc a) e = suc= (plus= a e)

-- NOTE: The next five functions are helper functions for `identity`.
-- (This is why I suggested you prove `identity` last.)

plus=' : {a b : Nat} → (c : Nat) → Nat= a b → Nat= (a + c) (b + c)
plus=' c zero= = refl c
plus=' c (suc= e) = suc= (plus=' c e)

plus-zero : (n : Nat) → Nat= (n + zero) n
plus-zero zero = zero=
plus-zero (suc n) = suc= (plus-zero n)

plus-assoc : (a b c : Nat) → Nat= ((a + b) + c) (a + (b + c))
plus-assoc zero b c = refl (b + c)
plus-assoc (suc a) b c = suc= (plus-assoc a b c)

plus-comm : (a b : Nat) → Nat= (a + b) (b + a)
plus-comm a zero = plus-zero a
plus-comm a (suc b) = trans (plus-suc a b) (suc= (plus-comm a b))

times-suc : (m n : Nat) → Nat= (m * suc n) (m + m * n)
times-suc zero _ = zero=
times-suc (suc m) n = suc=
  (trans (plus= n (times-suc m n))
  (trans (sym (plus-assoc n m (m * n)))
  (trans (plus=' (m * n) (plus-comm n m))
  (plus-assoc m n (m * n)))))

-- an identity of natural numbers. (** do this last **)
identity : (n : Nat) → Nat= ((1 + n) * (1 + n)) ((1 + n * 2) + n * n)
identity n = suc=
  (trans (plus= n (times-suc n n))
  (trans (sym (plus-assoc n n (n * n)))
  (plus=' (n * n) (sym (times2 n)))))

-- the sum of the first n terms of b is n^2.
b-sum : (n : Nat) → Nat= (sum n b) (n * n)
b-sum zero = zero=
b-sum (suc n) = trans (plus= (b n) (b-sum n))
  (sym (identity n))

