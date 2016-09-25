//@+ CheckArithOverflow = yes

/*@ predicate swapped{L1,L2}(int[] a, integer i, integer j) =
  @   \at(a[i],L1) == \at(a[j],L2) && \at(a[j],L1) == \at(a[i],L2);
  @*/

/*@ predicate swapped_rest_unchanged{L1,L2}(int[] a, integer i, integer j) =
  @   swapped{L1,L2}(a, i, j) &&
  @   \forall integer k; 0 <= k < a.length && k != i && k != j ==> \at(a[k],L1) == \at(a[k],L2);
  @*/

/*@ predicate reversed{L1,L2}(int[] a, integer low, integer high, integer max) =
  @   (\forall integer i; low <= i < high ==> swapped{L1,L2}(a, i, max - i)) &&
  @   (\forall integer k; high <= k <= max - high ==> \at(a[k], L1) == \at(a[k], L2));
  @*/

/*@ lemma reversed_after{L1,L2}:
  @ \forall int[] a;
  @ \forall integer i;
  @   reversed{L1,L2}(a, 0, i, a.length - 1) ==>
  @   0 <= i <= a.length - i + 1 ==>
  @   !(i <= a.length - 1 - i) ==>
  @   reversed{L1,L2}(a, 0, a.length/2, a.length - 1);
  @*/

/*@ lemma reversed_swapped_rest_unchanged_then_reversed{L2,L1,L}:
  @   \forall int[] a;
  @   \forall integer i;
  @     0 <= i <= a.length - 1 - i &&
  @     reversed{L,L1}(a, 0, i, a.length - 1) &&
  @     swapped_rest_unchanged{L1,L2}(a, i, a.length - 1 - i) ==>
  @     reversed{L,L2}(a, 0, i + 1, a.length - 1);
  @*/

public class Strings {

    /*@ requires 
      @   a != null && 0 <= i < a.length && 0 <= j < a.length;
      @
      @ assigns
      @   a[i], a[j];
      @
      @ ensures 
      @   swapped{Old,Here}(a, i, j);
      @*/
    public static void swap(int[] a, int i, int j) {
	int tmp = a[i];
	a[i] = a[j];
	a[j] = tmp;
    }

    /*@ requires 
      @   a != null;
      @
      @ assigns
      @   a[..];
      @
      @ ensures 
      @   reversed{Old,Here}(a, 0, a.length/2, a.length - 1);
      @*/
    public static void reverse(int[] a) {
	/*@ loop_invariant
	  @   reversed{Pre,Here}(a, 0, i, a.length - 1) && 0 <= i <= a.length - i + 1;
	  @
	  @ loop_variant
	  @   a.length - 1 - i;
	  @*/
	for (int i = 0; i <= a.length - 1 - i; i++) {
	    swap(a, i, a.length - 1 - i);
	}
    }

}
