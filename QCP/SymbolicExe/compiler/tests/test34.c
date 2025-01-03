//@ Extern Coq (option :: * => *)
//@ Extern Coq (zero : nat) (succ : nat -> nat)
//@ Extern Coq (some : {A} -> A -> option A) (none : {A} -> option A)

//@ Let In({A}; x : A, l : option A) = emp
//@ Let Eq({A}; x : option A, y : option A) = exists z, In(z, x) && In(z, y)

//@ Extern Coq (id : {A} -> A -> A)

int g()
/*@ With {M} {T}
         (bind : M (M T) -> (M T -> M T) -> M T) (x : M (M T)) p
    Require emp
    Ensure p(bind(x, id), x)
 */;

int f(int (*f)(int))
/*@ With p
    Require p(id(id): Z -> Z)
    Ensure f |= int (int x) With x0 Require x == x0 Ensure __return == x0
 */;

