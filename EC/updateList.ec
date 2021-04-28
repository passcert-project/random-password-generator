require import AllCore List.

op update (x : 'a) (s : 'a list) (n : int) =
  if n < 0 then s else (if size s <= n then s else take n s ++ x :: drop (n+1) s).


lemma size_update (x:'a) (string:'a list) (n:int):
    size string = size (update x string n).
proof.
smt.    
qed.
