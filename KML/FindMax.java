//@+ CheckArithOverflow = yes

public class FindMax {

    /*@ requires 
      @   a != null && a.length >= 1; 
      @
      @ assigns
      @   \nothing;
      @
      @ ensures  
      @   0 <= \result < a.length &&  
      @   \forall integer i; 0 <= i < a.length ==> a[i] <= a[\result]; 
      @*/
    public static int findMax(int[] a) { 
	int m = a[0]; 
	int r = 0; 
	/*@ loop_invariant  
	  @   1 <= i <= a.length && 0 <= r < a.length && m == a[r] &&
	  @   \forall integer j; 0 <= j < i ==> a[j] <= a[r]; 
	  @
	  @ loop_variant 
	  @   a.length - i;
	  @*/ 
	for (int i = 1; i < a.length; i++) { 
	    if (a[i] > m) { 
		r = i;  
		m = a[i]; 
	    } 
	} 
	return r; 
    } 

}
