//@+ CheckArithOverflow = yes

/*@ lemma mod2_div2: 
  @   \forall integer x y; x % 2 == y % 2 ==> (x + y)/2 - x == y - (x + y)/2;
  @*/

public class Mean {

    /*@ requires 
      @   x % 2 == y % 2;    
      @ 
      @ assigns
      @   \nothing;
      @
      @ ensures 
      @   \result == (x + y)/2;
      @*/
    public static int mean(int x, int y) {
	int i = x;
	int j = y;	
	/*@ loop_invariant 
	  @   (i < j ==> (x + y)/2 - i == j - (x + y)/2) && 
	  @   (i >= j ==> (x + y)/2 - j == i - (x + y)/2);
	  @
	  @ loop_variant 
	  @   i < j ? j - i : i - j;
	  @*/
	while (i != j) {
	    if (i < j) {		
		i = i + 1;
		j = j - 1;		
	    } else {		
		j = j + 1;
		i = i - 1;		
	    }	    
	}	
	return i;		
    }

}
