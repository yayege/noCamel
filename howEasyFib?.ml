

let rec inc (k:int) (n:int) = match n with
  | 0 -> (k:int)
  | _ ->  k + (inc k (n - 1)) + 1



let rec fib (n : int) = match n with
    0 -> 1
  | 1 -> 1
  | n -> fib (n - 1) + fib (n - 2)
