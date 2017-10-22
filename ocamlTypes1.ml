
type prop = Atom of string
          | Not of prop
          | And of prop * prop
          | Or of prop * prop

let impl (p, q) = Or(Not p, q)
let iff (p, q) = And (impl (p,q), impl (q, p))

let mp = impl (And (Atom "P", impl (Atom "P", Atom "Q")), Atom "Q")

(* Proof by contradiction (reduction ad absurdum): ((¬ P) ⇒ Q) ∧ ((¬ P) ⇒ (¬ Q)) ⇒ P *)
let ra = impl (
             And (impl (Not (Atom "P"),
                        Atom "Q"),
                  impl (Not (Atom "P"),
                        Not (Atom "Q"))),
             Atom "P")

(* Atoms and their negations *)
type signed_atom
  = PosAtom of string
  | NegAtom of string

(* In NNF negations can only be applied to atoms, this datatype only
   allows for propositions in NNF *)
type nnf
  = AndN of nnf * nnf
  | OrN of nnf * nnf
  | AtomN of signed_atom


let rec to_nnf : prop -> nnf = function
  | Atom a -> AtomN (PosAtom a)
  | Not (Atom a) -> AtomN (NegAtom a)
  | Not(Not a) -> to_nnf a 
  | Not(And(p, q)) -> OrN(to_nnf (Not p), to_nnf (Not q))
  | Not(Or(p, q)) -> AndN(to_nnf (Not p), to_nnf (Not q))
  | And(p, q) -> AndN(to_nnf p, to_nnf q)
  | Or(p, q) -> OrN(to_nnf p, to_nnf q)



type cnf 
  = AndC of cnf * cnf
  | OrC of cnf * cnf 
  | AtomC of signed_atom


let rec distribute : cnf * cnf -> cnf = function
  | p, AndC(q, r) -> AndC(distribute(p, q), distribute(p, r))
  | AndC(q, r), p -> AndC(distribute(q, p), distribute(r, p))
  | p,q -> OrC(p,q)

let rec nnf_to_cnf : nnf -> cnf = function
  | AndN(p, q) -> AndC(nnf_to_cnf p, nnf_to_cnf q)
  | OrN(p, q) -> distribute(nnf_to_cnf p, nnf_to_cnf q)
  | AtomN a ->AtomC a

let to_cnf (p :prop) : cnf = nnf_to_cnf (to_nnf p)


let rec positives = function
  | AtomC(PosAtom a) -> [a]
  | AtomC(NegAtom _) -> [] 
  | OrC(p, q) -> positives p @ positives q
  | AndC(p,q)-> positives p @ positives q

let rec negatives = function
  | AtomC(PosAtom _) -> []
  | AtomC(NegAtom a) -> [a] 
  | OrC(p, q) -> negatives p @ negatives q
  | AndC(p,q)-> negatives p @ negatives q

(* Fill in the code for the intersection function from Q1.1 *)
let rec contains x l = match l with 
  [] -> false
  | h::t -> (x = h) || contains x t

let rec intersection (l1 : 'a list) (l2 : 'a list) : 'a list = match l1 with
  [] -> []
  | h::t -> if (contains h l2) then h::(intersection t l2) else intersection t l2


let rec cnf_tautology : cnf -> bool = function
  | AndC(p, q) -> cnf_tautology p && cnf_tautology q
  | p -> ([] = intersection (positives p) (negatives p))
  

let taut (p : prop) : bool = cnf_tautology (to_cnf p)
let unsat (p : prop) : bool = taut (Not p)
let sat (p : prop) : bool = not (unsat p) 
