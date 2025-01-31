module Int2 where

-- import `plus` & `times` on Nats;
-- use these functions where appropriate below.
open import Nat

data Int : Set where
  -- (+ n) represents positive n.
  + : Nat → Int
  -- (- n) represents negative n.
  - : Nat → Int
  -- 0 can be represented as (+ zero) or (- zero).

-- given i, return i + 1.
isuc : Int → Int
isuc (+ n) = + (suc n)
isuc (- zero) = + (suc zero)
isuc (- (suc n)) = - n

-- given i, return i - 1.
ipred : Int → Int
ipred (+ (suc n)) = + n
ipred (-  n) = - (suc n) 
ipred (+ zero) = - zero

-- given i, return -i.
ineg : Int → Int
ineg (- n) = + n
ineg (+ n) = - n

-- given i & j, return i + j.
-- there's probably a more efficient way to do this, but this is what I got!
iplus : Int → Int → Int
iplus (+ a) (+ b) = + (plus a b)
iplus (- a) (- b) = - (plus a b)
iplus (+ (suc a)) (- (suc b)) = {! iplus (+ a) (- b) !}
iplus (+ a) (- zero) = + a
iplus (+ zero) (- b) = - b
iplus (- (suc a)) (+ (suc b)) = {! iplus (- a) (+ b) !}
iplus (- a) (+ zero) = - a
iplus (- zero) (+ b) = + b

-- given i & j, return i - j.
iminus : Int → Int → Int
iminus (+ (suc a)) (+ (suc b)) = iminus (+ a) (+ b)
iminus (+ a) (+ zero) = + a
iminus (+ zero) (+ b) = + b
iminus (- (suc a)) (- (suc b)) = iminus (- a) (- b)
iminus (- a) (- zero) = - a
iminus (+ a) (- zero) = + a
iminus (+ a) (- b) = {! + (plus a b) !}
iminus (- a) (+ b) = - (plus a b)
iminus (- zero) (- b) = + b


-- given i & j, return i * j.
itimes : Int → Int → Int
itimes (+ a) (+ b) = + (times a b)
itimes (- a) (- b) = + (times a b)
itimes (- a) (+ b) = - (times a b)
itimes (+ a) (- b) = - (times a b)


