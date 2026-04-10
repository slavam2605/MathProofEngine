# Proof Goals

This document is a long-term backlog of theorem targets for the engine.

The goals are grouped by rough proof complexity:

- Level 1: direct axiom use and short equality/order chains
- Level 2: multi-step symbolic manipulations
- Level 3: induction or witness-based reasoning with reusable lemmas
- Level 4: typical school-style written proofs
- Level 5: harder school-level challenge proofs

Many goals below depend on definitions that should be formalized as reusable statements first (for example `Divides`, `Prime`, `sumTo`, `oddSum`, `gcd`, finite set/product operators).

## TODO (Axiom Debt)

- `ordered-field-zero-le-one-from-theory`: replace the current trusted `0 <= 1` axiom (`zeroLeOne`) with a proved theorem.

## Already Formalized In Repository

- `nat-add-zero-left`: `forall n:Nat, 0 + n = n` (in `NatLibrary`)
- `nat-add-assoc`: `forall a b c:Nat, (a + b) + c = a + (b + c)` (in `NatTheory`)
- `nat-add-comm`: `forall a b:Nat, a + b = b + a` (in `NatTheory`)
- `nat-left-distrib`: `forall a b c:Nat, a*(b + c) = a*b + a*c` (in `NatTheory`)
- `nat-zero-sum`: `forall a b:Nat, a + b = 0 -> (a = 0 and b = 0)` (in `NatLibrary`)
- `nat-mul-one-right`: `forall n:Nat, n * 1 = n` (in `NatTheory`)

## Level 1

- `real-order-translation`: `forall x y z:Real, x <= y -> x + z <= y + z`
- `real-sqrt-exists`: `forall x:Real, 0 <= x -> exists y:Real, y*y = x`

## Level 2

- `nat-divides-linear-combo`: `forall a b c:Nat, Divides(a,b) and Divides(a,c) -> Divides(a, b + c)`
- `real-order-transitive`: `forall x y z:Real, x <= y and y <= z -> x <= z`
- `real-neg-reverses-order`: `forall x y:Real, x <= y -> -y <= -x`

## Level 3

- `real-square-nonnegative`: `forall x:Real, 0 <= x*x`
- `real-zero-product-square`: `forall x:Real, x*x = 0 -> x = 0`

## Level 4 (School Proofs)

- `nat-sum-first-n`: `forall n:Nat, 2 * sumTo(n) = n * (n + 1)`
- `nat-sum-first-odd`: `forall n:Nat, oddSum(n) = n * n` where `oddSum(n)=1+3+...+(2n-1)`
- `nat-divides-linear-combo` (full witness proof style): `forall a b c:Nat, Divides(a,b) and Divides(a,c) -> Divides(a, b + c)`
- `real-square-difference-nonnegative`: `forall x y:Real, 0 <= (x - y)*(x - y) -> 2*x*y <= x*x + y*y`
- `real-order-translation` (as a reusable tactic-level theorem): `forall x y z:Real, x <= y -> x + z <= y + z`

## Level 5 (Harder School Challenges)

- `nat-cube-minus-self-divisible-by-6`: `forall n:Nat, Divides(6, n*n*n - n)`
- `infinitely-many-primes`: `forall finiteSet P of Nat, exists p:Nat, Prime(p) and not In(p,P)`
- `real-am-gm-two-variables`: `forall a b:Real, 0 <= a and 0 <= b -> 2*sqrt(a*b) <= a + b`
- `real-quadratic-root-verification`: `forall a b c:Real, a != 0 and 0 <= b*b - 4*a*c -> let x = (-b + sqrt(b*b - 4*a*c)) / (2*a) in a*x*x + b*x + c = 0`
- `irrational-sqrt2`: `not (exists p q:Nat, q != 0 and gcd(p,q)=1 and p*p = 2*q*q)`

## Additional Future Domain Goals

- Group: `forall a, a * e = a`; `forall a, a * inv(a) = e`
- Ring: `forall a, a*0 = 0`; `forall a b, -(a+b) = (-a)+(-b)`
- Number theory: `forall n, even(n) or odd(n)`; `Divides(a,b) and Divides(b,c) -> Divides(a,c)`
- Set/function theory: `A subset B and B subset C -> A subset C`; `injective(f) -> (f(x)=f(y) -> x=y)`

## Usage Notes

- Treat each item as a future `statement("...")` target with a stable theorem id.
- For each new theorem family, add:
  - one worked example proof in `src/main/.../examples`
  - one misuse/failing test that demonstrates rule boundaries
