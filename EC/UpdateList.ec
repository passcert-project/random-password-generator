require import AllCore List Ring IntDiv StdOrder.
import Ring.IntID IntOrder.

op update (x : 'a) (s : 'a list) (n : int) =
  if n < 0 then s else (if size s <= n then s else take n s ++ x :: drop (n+1) s).

lemma drop_plus1_size (x:'a) (string:'a list) (n:int) :
  0 <= n =>
  n < size string =>
  size (drop (n+1) string) = size (drop n string) - 1.
proof.
move => h1 h2.
rewrite (drop_nth x n string).
split. assumption. move => h3. assumption.
by simplify.
qed.


lemma update_empty (x:'a) (n:int) :
  update x [] n = [].
proof.
case (n < 0).
- move => h1.
  by rewrite /update h1 /=.
- move => h1.
  by rewrite /update h1 /= lezNgt h1 /=.
qed.


lemma update_size (x:'a) (string:'a list) (n:int) :
  size string = size (update x string n).
proof.
rewrite /update.
case (n < 0).
- trivial.
- move => h1.
  case (size string <= n).
  + trivial.
  + move => h2.
    rewrite size_cat /= (drop_plus1_size x string n).    
    + by rewrite -lezNgt in h1.
      by rewrite -ltzNge in h2.
    by rewrite /= -size_cat cat_take_drop.
qed.


lemma update_id (x:'a) (string:'a list) (n:int) :
  update (nth x string n) string n = string.
proof.
rewrite /update.
case (n < 0).
- trivial.
- case (size string <= n).
  + trivial.
  + move => h1 h2.
    rewrite -(drop_nth x n string).
    split.
    * by rewrite -lezNgt in h2.
    * by rewrite -ltzNge in h1.
    apply cat_take_drop.
qed.
