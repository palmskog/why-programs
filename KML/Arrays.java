//@+ CheckArithOverflow = yes

/*@ predicate insertion_point{L}(integer ip, int key, int[] a) =
  @   0 <= ip <= a.length &&
  @   (\forall integer i; 0 <= i < ip ==> a[i] < key) &&
  @   (\forall integer i; ip <= i < a.length ==> key < a[i]);
  @*/

/*@ predicate sorted{L}(int[] a, integer low, integer high) =
  @   \forall integer i; low <= i < high ==> a[i] <= a[i + 1];
  @*/

/*@ lemma mean_le:
  @ \forall integer i; 
  @ \forall integer j;
  @   i <= j ==> 
  @   i <= i + ((j - i) / 2) <= j;
  @*/

/*@ lemma sorted_array_index_elt_le{L}:
  @   \forall int[] a; 
  @     sorted{L}(a, 0, a.length - 1) ==> 
  @     \forall integer i; 
  @     \forall integer j;
  @       0 <= i <= a.length - 1 ==>
  @       0 <= j <= a.length - 1 ==> 
  @       i <= j ==>
  @       a[i] <= a[j];
  @*/

/*@ lemma sorted_array_index_lt{L}:
  @   \forall int[] a; 
  @     sorted{L}(a, 0, a.length - 1) ==> 
  @     \forall integer i;
  @     \forall integer j;
  @       0 <= i <= a.length - 1 ==>
  @       0 <= j <= a.length - 1 ==>
  @       a[i] < a[j] ==>
  @       i < j;
  @*/

public class Arrays {
        
    /*@ requires 
      @   a != null && sorted(a, 0, a.length - 1);
      @
      @ assigns
      @   \nothing;
      @
      @ behavior has_key: 
      @   assumes
      @     \exists integer i; 0 <= i <= a.length - 1 && a[i] == key;
      @   ensures
      @     a[\result] == key;
      @ 
      @ behavior has_not_key:
      @   assumes 
      @     \forall integer i; 0 <= i <= a.length - 1 ==> a[i] != key;
      @   ensures
      @     insertion_point(-\result - 1, key, a);
      @*/
    public static int binarySearch(int[] a, int key) {
	int low = 0;
 	int high = a.length - 1;
	/*@ loop_invariant 
	  @   0 <= low && high <= a.length - 1;
	  @
	  @ for has_key:
	  @   loop_invariant
	  @     \exists integer i; low <= i <= high && a[i] == key; 
	  @   
	  @ for has_not_key:
	  @   loop_invariant 
	  @     low <= a.length &&
	  @     (\forall integer i; 0 <= i < low ==> a[i] < key) &&
	  @     (\forall integer i; high < i <= a.length - 1 ==> key < a[i]);
	  @     
	  @ loop_variant 
	  @   high - low;
	  @*/
	while (low <= high) {
	    int mid = low + ((high - low) / 2);
	    int midVal = a[mid];	    
	    if (midVal < key) {
		low = mid + 1;
	    } else if (midVal > key) {
		high = mid - 1;
	    } else {
		return mid;
	    }
	}		
	return -low - 1;
    }

}
