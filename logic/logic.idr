
%default total


-- To get very far with classical looking logic / proofs,
-- we need to include 1 postulate: The Law of Excluded Middle (LEM) (https://en.wikipedia.org/wiki/Law_of_excluded_middle)
-- The most direct way to write this in Idris is like so:
-- lawOfExcludedMiddle : (p : Type) -> Either p (Not p)

-- However, if we include this function, then everywhere we can use the LEM.
-- Instead, we can write it as an interface, and then any proof
-- that depends on the LEM can include it as a constraint. Any proof that
-- does NOT need the LEM doesn't need the constraint.
-- Then, we can seperate out which proofs have been done fully constructively vs classically.
-- If this is too much of a pain in the ass we can change it.

interface LEM (prop : Type) where
    lawOfExcludedMiddle : Dec prop

-- To automatically turn on LEM for all types, just uncomment this.
-- implementation LEM p where
--     lawOfExcludedMiddle = ?awerqwer



-- Prove some basics of negation
-- Note that this direction uses the LEM
notNot : LEM a => (Not (Not a)) -> a
notNot {a} x = case lawOfExcludedMiddle {prop=a} of
    Yes prf => prf
    No contra => void $ x contra

-- But this direction doesn't use the LEM
notNotBack : a -> Not (Not a)
notNotBack x = \f => f x

-- Prove contraposition in both directions
contrapositionBack : (p -> q) -> ((Not q) -> (Not p))
contrapositionBack f nq = nq . f

congNot : {f : t -> u} -> Not (f a = f b) -> Not (a = b)
congNot = contrapositionBack cong

-- This also gives a convenient tool for writing proofs by contraposition
proofByContraposition : LEM q => ((Not q) -> (Not p)) -> (p -> q)
proofByContraposition {q} f x =
    let q' = (flip f) x in
    notNot q'

-- Now we define what it means for two propositions p and q to be iff
-- The operator p <-> q denotes the proposition: Iff p q
-- Who knows what the right precendence level is???
infixl 4 <->
record (<->) p q where
    constructor MkIff
    ltr : p -> q
    rtl : q -> p

iffReflexive : a <-> a
iffReflexive = MkIff id id

iffSymmetric : (p <-> q) -> (q <-> p)
iffSymmetric pq = MkIff (rtl pq) (ltr pq)

iffTransitive : (p <-> q) -> (q <-> r) -> (p <-> r)
iffTransitive pq qr = MkIff (ltr qr . ltr pq) (rtl pq . rtl qr)

-- We define the operator <=> which is just an infix version of iffTransitive
-- The idea is that we can use this to write proofs that look more math-y
-- As an example, see s3EqIff below.
infixl 4 <=>
(<=>) : (p <-> q) -> (q <-> r) -> (p <-> r)
(<=>) pq qr = iffTransitive pq qr


-- Now we show that <-> holds for some basic things.
notNotIff : LEM p => p <-> Not (Not p)
notNotIff {p} = MkIff notNotBack notNot

contrapositionIff : LEM q => (p -> q) <-> ((Not q) -> (Not p))
contrapositionIff = MkIff contrapositionBack proofByContraposition


-- We now prove de Morgan's laws
deMorganAnd : (LEM a, LEM b) => Not (a, b) -> Either (Not a) (Not b)
deMorganAnd {a} {b} contra = case (lawOfExcludedMiddle {prop=a}, lawOfExcludedMiddle {prop=b}) of
    (Yes aPrf, Yes bPrf) => void $ contra (aPrf, bPrf)
    (_, No bContra) => Right bContra
    (No aContra, _) => Left aContra

deMorganOr : Not (Either a b) -> (Not a, Not b)
deMorganOr x = (x . Left, x . Right)

-- A small lemma that (q, Not q) is a contradiction
trueAndFalse : Not (q, Not q)
trueAndFalse = \pr => (snd pr) (fst pr)

-- This formalizes proof by contradiction,
-- and hopefully gives a convenient proof construact for doing proof by contradiction.
proofByContradiction : LEM p => (Not p -> (q, Not q)) -> p
proofByContradiction {p} f =
    let g = trueAndFalse . f in
    notNot g


------------ Below are some example proofs --------------

-- This is a small lemma
succEqIff : (n : Nat) -> (k : Nat) -> (n = k) <-> (S n = S k)
succEqIff {n} {k} = MkIff cong (succInjective n k)

-- Here is an example iff style proof.
s3EqIff : (n : Nat) -> (k : Nat) -> (n = k) <-> (S (S (S n)) = S (S (S k)))
s3EqIff n k =
    (succEqIff n k)
    <=> (succEqIff (S n) (S k))
    <=> (succEqIff (S (S n)) (S (S k)))


-- This is a lemma used in the below proofs
minusCancel : (n : Nat) -> (m : Nat) -> minus (n + m) n = m
minusCancel Z m = minusZeroRight m
minusCancel (S j) m = minusCancel j m

-- Here is an example proof, not using contraposition
plusPositiveNat : (n : Nat) -> (k : Nat) -> Not (k = Z) -> Not ((n + k) = Z)
plusPositiveNat n Z kNotZ = void $ kNotZ Refl
plusPositiveNat n (S k) skNotZ = \prf =>
    let g = minusCancel n (S k) in
    let prf2 = cong {f = \m => minus m n} prf in
    let prf3 = trans (sym g) prf2 in
    skNotZ prf3


-- Here is the same proof using contraposition backwards
plusPositiveNatContrapositionBack : (n : Nat) -> (k : Nat) -> Not (k = Z) -> Not ((n + k) = Z)
plusPositiveNatContrapositionBack n k = contrapositionBack $
    \nkZ =>
        rewrite sym (minusCancel n k) in
        cong {f = \m => minus m n} nkZ
