open Nat

def exercise1 (A B : Prop):(A → False) → (A ∧ B) → False :=
    fun f p => f p.left


#check exercise1


def exercise2 (A : Prop): A → (A → False) → False :=
    fun x f => f x

#check exercise2



def ack : Nat →  Nat  → Nat
    | 0,n       => n+1
    | m+1, 0    => ack m 1
    | m+1, n+1  => ack m (ack (m+1) n)

def iter : Nat → (Nat → Nat)→(Nat → Nat)
    | 0, f      => f
    | n+1, f    => f ∘ iter n f

def ack2: Nat →  Nat  → Nat
    | 0,n       => n+1
    | m+1,n     => (iter n (ack2 m)) 1

#eval ack 0 1
#eval ack 4 0
#eval ack 3 2
#eval ack 0 1
#eval ack2 4 0
#eval ack 3 2
