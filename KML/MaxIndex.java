//@+ CheckArithOverflow = yes

public class MaxIndex {

    /*@ requires 
      @   a != null;
      @
      @ assigns 
      @   \nothing;
      @
      @ ensures 
      @   \forall integer i; 0 <= i < a.length ==> a[i] <= a[\result]; 
      @*/
    public static int maxIndex(int[] a) {
	int max = 0;
	int j = 1;

	/*@ loop_invariant 
	  @   0 <= max < j && \forall integer i; 0 <= i < j ==> a[i] <= a[max];
	  @
	  @ loop_variant
	  @   a.length - j;
	  @*/
	while (j < a.length) {	    
	    if (a[j] > a[max]) {
		max = j;
	    }	    
	    j++;
	}
	return max;
    }

}
