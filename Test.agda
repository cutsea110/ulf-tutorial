module Test where

open import Data.Nat hiding (compare)

-- view type
data Parity : ℕ → Set where
  even : (k : ℕ) → Parity (k * 2)
  odd  : (k : ℕ) → Parity (1 + k * 2)
-- view function
parity : (n : ℕ) → Parity n
parity zero = even zero
parity (suc n) with parity n
parity (suc .(k * 2)) | even k = odd k
parity (suc .(1 + k * 2)) | odd k = even (suc k)

-- how to use
half : ℕ → ℕ
half n with parity n
half .(k * 2) | even k = k
half .(1 + k * 2) | odd k = k

-- view type
data Compare : ℕ → ℕ → Set where
  less : ∀ {n} k → Compare n (n + suc k)
  more : ∀ {n} k → Compare (n + suc k) n
  same : ∀ {n} → Compare n n
-- view function
compare : (n m : ℕ) → Compare n m
compare zero zero = same
compare zero (suc m) = less m
compare (suc n) zero = more n
compare (suc n) (suc m) with compare n m
compare (suc n) (suc .(n + suc k)) | less k = less k
compare (suc .(m + suc k)) (suc m) | more k = more k
compare (suc m) (suc .m) | same = same

-- how to use
diff : ℕ → ℕ → ℕ
diff n m with compare n m
diff n .(n + suc k) | less k = suc k
diff .(m + suc k) m | more k = suc k
diff m .m | same = zero

-- view type
open import Data.List
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- prepare
data All {A : Set}(P : A → Set) : List A → Set where
  ∅ : All P []
  _:all:_ : ∀ {x xs} → P x → All P xs → All P (x ∷ xs)


isTrue : Bool → Set
isTrue false = ⊥
isTrue true = ⊤
isFalse : Bool → Set
isFalse false = ⊤
isFalse true = ⊥

lemmaT : ∀ {x} → x ≡ true → isTrue x
lemmaT refl = tt
lemmaF : ∀ {x} → x ≡ false → isFalse x
lemmaF refl = tt

open import Function using (_∘_)

data Inspect {A : Set}(x : A) : Set where
  _with-≡_ : (y : A) → x ≡ y → Inspect x
inspect : {A : Set}(x : A) → Inspect x
inspect x = x with-≡ refl

-- view
data Find {A : Set}(p : A → Bool) : List A → Set where
  found : (xs : List A)(y : A) → isTrue (p y) → (ys : List A)
          → Find p (xs ++ y ∷ ys)
  not-found : ∀ {xs} → All (isFalse ∘ p) xs → Find p xs
-- view function
find : {A : Set} (p : A → Bool) → (xs : List A) → Find p xs
find p [] = not-found ∅
find p (x ∷ xs) with inspect (p x)
find p (x ∷ xs) | true with-≡ px≡true
  = found [] x (lemmaT px≡true) xs
find p (x ∷ xs) | false with-≡ px≡false with find p xs
find p (x ∷ .(xs ++ y ∷ ys)) | false with-≡ px≡false | found xs y prf ys
  = found (x ∷ xs) y prf ys
find p (x ∷ xs) | false with-≡ px≡false | not-found npxs
  = not-found ((lemmaF px≡false) :all: npxs)

-- how to use
open import Data.Maybe

lookup : {A : Set} → (A → Bool) → List A → Maybe A
lookup p xs with find p xs
lookup p .(xs ++ y ∷ ys) | found xs y x ys = just y
lookup p xs | not-found npxs = nothing

even? : ℕ → Bool
even? n with parity n
even? .(k * 2) | even k = true
even? .(suc (k * 2)) | odd k = false
