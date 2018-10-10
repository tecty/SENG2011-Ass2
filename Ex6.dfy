predicate Sorted(a:array<int>, low:int, high:int) 
    reads a 
    // index must not out of bound 
    requires 0 <=low
    requires     high <= a.Length
{
    forall i :: low <= i< high-1 ==> a[i]<= a[i+1]
}
