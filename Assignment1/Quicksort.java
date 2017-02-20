public class Quicksort {

    // Write formal pre- and post-conditions for this method.
    /*@ modifies a[*];
      @ requires a != null;
      @ requires (\forall int n; 0 <= n && n < a.length ; a[n] <= ulimit);
      @ requires (\forall int n; 0 <= n && n < a.length ; a[n] >= llimit);
      @ ensures(\forall int n; 0 < n && n < a.length;  a[n-1] <= a[n]);
    @*/
    public static void sort(int[] a, int ulimit, int llimit)
    {
        quicksort(a, 0, a.length, ulimit, llimit);
    }
    
    
    // Write pre-conditions for this method.
    /*@ requires start >= 0;
      @ requires stop <= a.length;
      @ requires a != null;
      @ requires (\forall int n; n >= start && n < stop ; a[n] <= ulimit);
      @ requires (\forall int n; n >= start && n < stop ;  a[n] >= llimit);
    @*/
    //@ modifies a[*];
    // Write post-conditions for this method.
    /*@ ensures (\forall int n ; start < n && n < stop  ; a[n-1] <= a[n]);
      @ ensures (\forall int n ; n >= start && n < stop; a[n] <= ulimit);
      @ ensures (\forall int n ; n >= start && n < stop; a[n] >= llimit);
 	  @ ensures (\forall int n ; n >= 0 && n < start ; a[n] == \old(a[n]));
      @ ensures (\forall int n ; n >= stop && n < a.length ; a[n] == \old(a[n]));
    @*/
    private static void quicksort(int[] a, int start, int stop, int ulimit, int llimit)
    {
        if (stop - start > 1) {
            int p = pivot(a, start, stop, ulimit, llimit);
            quicksort(a, start, p, a[p], llimit);
            quicksort(a, p+1, stop, ulimit, a[p]);
        }
    }

    // Write pre-conditions for this method.
    /*@ requires stop <= a.length;
      @ requires start >= 0;
      @ requires start < stop;
      @ requires a != null;
      @ requires (\forall int n; n >= start && n < stop; a[n] <= ulimit);
      @ requires (\forall int n; n >= start && n < stop;  a[n] >= llimit);
    @*/
    //@ modifies a[*];
    // Write post-conditions for this method.
    /*@ ensures start <= \result;
      @ ensures \result < stop;
      @ ensures (\forall int n ; n >= start && n < stop ; a[n] >= llimit);
      @ ensures (\forall int n ; n >= start && n < stop; a[n] <= ulimit);
      @ ensures (\forall int n ; n >= start && n < \result ; a[n] <= a[\result]);
      @ ensures (\forall int n ; n > \result && n < stop; a[n] >= a[\result]);
      @ ensures (\forall int n ; n >= 0 && n < start ; a[n] == \old(a[n]));
      @ ensures (\forall int n ; n >= stop && n < a.length ; a[n] == \old(a[n]));
    @*/
    private static int pivot(int[] a, int start, int stop, int ulimit, int llimit)
    {
        int p = partition(a, a[start], start+1, stop, ulimit, llimit);
        if (start < p)
            swap(a, start, p);
        return p;
    }

    // Write pre-conditions for this method.
    /*@	requires a != null;
      @ requires stop <= a.length;
      @ requires start >= 0;
      @ requires start <= stop;
      @ requires (\forall int n ; n >= start && n < stop ; a[n] <= ulimit);
      @ requires (\forall int n ; n >= start && n < stop ; a[n] >= llimit);
    @*/
    //@ modifies a[*];
    // Write post-conditions for this method.
    /*@ ensures \result < stop;
      @ ensures \result >= start - 1;
      @ ensures (\forall int n ; n >= start && n < stop ; a[n] <= ulimit);
      @ ensures (\forall int n ; n >= start && n < stop ; a[n] >= llimit);
      @ ensures (\forall int n ; n >= start && n <= \result ; a[n] <= pivot);
      @ ensures (\forall int n ; n > \result && n < stop ; a[n] >= pivot);
      @ ensures (\forall int n ; n >= 0 && n < start ; a[n] == \old(a[n]));
      @ ensures (\forall int n ; n >= stop && n < a.length ; a[n] == \old(a[n]));
    @*/
    private static int partition(int[] a, int pivot, int start, int stop, int ulimit, int llimit)
    {
        if (start >= stop) 
            return start - 1;
        if (a[start] < pivot)
            return partition(a, pivot, start + 1, stop, ulimit, llimit);
        if (a[--stop] > pivot)
            return partition(a, pivot, start, stop, ulimit, llimit);
        if (start < stop) {
            swap(a, start, stop);
            return partition(a, pivot, start+1, stop, ulimit, llimit);
        } else
            return start;
    }

    /*@ requires a != null;
      @ requires 0 <= i && i < a.length;
      @ requires 0 <= j && j < a.length;
      @ modifies a[i], a[j];
      @ ensures a[i] == \old(a[j]) && a[j] == \old(a[i]);
      @*/
    public static void swap(int[] a, int i, int j)
    {
        int temp = a[i];
        a[i] = a[j];
        a[j] = temp;
    }
}
