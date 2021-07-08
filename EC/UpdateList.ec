require import AllCore List.

op update (x : 'a) (s : 'a list) (n : int) =
  if n < 0 then s else (if size s <= n then s else take n s ++ x :: drop (n+1) s).

(* auxiliary lemma on drop size *)
lemma drop_plus1_size (x:'a) (string:'a list) (n:int) :
  0 <= n =>
  n < size string =>
  size (drop (n+1) string) = size (drop n string) - 1.
proof.
smt.
qed.  


lemma update_empty (x:'a) (n:int) :
  update x [] n = [].
proof.
case (n < 0).
- move => ?.
  rewrite /update.
  rewrite H.
  by simplify.
- move => ?.
  rewrite /update.
  rewrite H.
  simplify.
  rewrite lezNgt.
  rewrite H.
  by simplify.
qed.


lemma update_size (x:'a) (string:'a list) (n:int) :
  size string = size (update x string n).
proof.
rewrite /update.
case (n < 0).
- trivial.
- move => ?.
  case (size string <= n).
  + trivial.
  + move => ?.
    rewrite size_cat.
    simplify.
    rewrite (drop_plus1_size x string n).    
    + by rewrite -lezNgt in H.
      by rewrite -ltzNge in H0.
    simplify.
    smt. (*completar, nao é dificil*)   
qed.


lemma update_id (x:'a) (string:'a list) (n:int) :
  update (nth x string n) string n = string.
proof.
rewrite /update.
case (n < 0).
- trivial.
- case (size string <= n).
  + trivial.
  + move => ? ?.
    rewrite -(drop_nth x n string).
    split.
    * by rewrite -lezNgt in H0.
    * by rewrite -ltzNge in H.
    apply cat_take_drop.
qed.
