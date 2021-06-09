require import AllCore List.

op update (x : 'a) (s : 'a list) (n : int) =
  if n < 0 then s else (if size s <= n then s else take n s ++ x :: drop (n+1) s).


lemma size_update (x:'a) (string:'a list) (n:int):
    size string = size (update x string n).
proof.
smt.    
qed.

(*lemma update_switch (x:'a) (string:'a list) (i j:int) :
  0 < i =>
  i <= size string =>
  0 <= j =>
  j < i =>
  take j string = take j (update (nth x string (i - 1))
                  (update (nth x string j) string (i - 1)) j).
proof.
move => H1 H2 H3 H4.
smt.
qed.*)

axiom update_perm_eq (x:'a) (string:'a list) (i j:int) :
  0 < i =>
  i <= size string =>
  0 <= j =>
  j < i =>
  perm_eq (update (nth x string (i - 1)) (update (nth x string j) string (i - 1)) j) string.

