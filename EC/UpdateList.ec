require import AllCore List Ring IntDiv StdOrder.
import Ring.IntID IntOrder.

op update (x : 'a) (s : 'a list) (n : int) =
  if n < 0 then s else (if size s <= n then s else take n s ++ x :: drop (n+1) s).

(*---------------------------------------------------------------------------------*)

lemma drop_plus1_size (x:'a) (s:'a list) (n:int) :
  0 <= n =>
  n < size s =>
  size (drop (n+1) s) = size (drop n s) - 1.
proof.
move => h1 h2.
rewrite (drop_nth x n s).
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


lemma update_id (x:'a) (s:'a list) (n:int) :
  update (nth x s n) s n = s.
proof.
rewrite /update.
case (n < 0).
- trivial.
- case (size s <= n).
  + trivial.
  + move => h1 h2.
    rewrite -(drop_nth x n s).
    split.
    * by rewrite -lezNgt in h2.
    * by rewrite -ltzNge in h1.
    apply cat_take_drop.
qed.


lemma size_update (x:'a) (s:'a list) (n:int) :
  size s = size (update x s n).
proof.
rewrite /update.
case (n < 0).
- trivial.
- move => h1.
  case (size s <= n).
  + trivial.
  + move => h2.
    rewrite size_cat /= (drop_plus1_size x s n).    
    + by rewrite -lezNgt in h1.
      by rewrite -ltzNge in h2.
    by rewrite /= -size_cat cat_take_drop.
qed.


lemma nth_update (x:'a) (s:'a list) (i j:int) :
  nth x s i = nth x (update (nth x s i) s j) i.
proof.
rewrite /update.
case (j < 0).
- trivial.
- case (size s <= j).
  + trivial.
  + move => h1 h2.
    rewrite lerNgt /= in h1.
    rewrite ltrNge /= in h2.
    case (i < j).
    - move => h3.
      rewrite nth_cat size_takel.
      split. assumption. rewrite ltr_neqAle in h1. case h1. move => *. assumption.
      by rewrite h3 /= nth_take.
    - case (j < i).
      + move => h3 h4.        
        rewrite nth_cat size_takel.
        split. assumption. rewrite ltr_neqAle in h1. case h1. move => *. assumption.
        rewrite h4 /=.
        have h5 : ! i-j = 0.
        * smt().
        rewrite h5 /= nth_drop.
        smt(). smt().
        have h6 : j + 1 + (i - j - 1) = i.
        * ring.
        by rewrite h6.
      + move => h3 h4.
        have h5 : i = j.
        smt().
        subst.
        rewrite -(drop_nth x j s).
        split. assumption. move => *. assumption.
        by rewrite cat_take_drop.
qed.
