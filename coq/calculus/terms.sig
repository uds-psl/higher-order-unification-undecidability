type : Type
exp : Type
nat : Type
X : Type

const : X -> exp
lam : (exp -> exp) -> exp 
app : exp -> exp -> exp 

typevar : nat -> type
arr : type -> type -> type
